import 'dart:collection';
import 'dart:math';

enum StressLevel { low, medium, high }

class StressInferenceResult {
  final double stressProbability;
  final double cortisolProxy;
  final double confidence;
  final StressLevel level;
  final bool calibrationReady;

  const StressInferenceResult({
    required this.stressProbability,
    required this.cortisolProxy,
    required this.confidence,
    required this.level,
    required this.calibrationReady,
  });

  String get levelText {
    switch (level) {
      case StressLevel.low:
        return 'Low';
      case StressLevel.medium:
        return 'Medium';
      case StressLevel.high:
        return 'High';
    }
  }
}

class StressEngine {
  static const int _minInferenceSamples = 4;
  final int windowSize;
  final int stepSize;
  final int baselineWindows;

  final Queue<_SensorPoint> _points = Queue<_SensorPoint>();
  final Queue<_CalibWindow> _calibWindows = Queue<_CalibWindow>();
  int _calibrationValidCount = 0;

  int _samplesSinceInference = 0;
  int _syntheticTs = 0;

  bool _calibrationMode = false;
  double? _smoothedProb;

  _LogisticModel? _trainedLogistic;
  _RandomForestModel? _trainedForest;
  _BaselineStats? _baseline;

  StressEngine({
    this.windowSize = 20,
    this.stepSize = 1,
    this.baselineWindows = 12,
  });

  void reset() {
    _points.clear();
    _samplesSinceInference = 0;
    _syntheticTs = 0;
    _smoothedProb = null;
  }

  void setCalibrationMode(bool enabled) {
    _calibrationMode = enabled;
  }

  void resetCalibration() {
    _calibWindows.clear();
    _calibrationValidCount = 0;
    _baseline = null;
  }

  Map<String, dynamic>? exportCalibration() {
    final b = _baseline;
    if (b == null) return null;
    return {
      'baseline_hr_mean': b.hrMean,
      'baseline_eda_mean': b.edaMean,
      'baseline_temp_mean': b.tempMean,
      'baseline_hr_std': b.hrStd,
      'baseline_eda_std': b.edaStd,
      'baseline_temp_std': b.tempStd,
      'windows': _calibrationValidCount,
      'target': baselineWindows,
      'version': 1,
    };
  }

  bool loadCalibration(Map<String, dynamic> json) {
    final hrM = (json['baseline_hr_mean'] as num?)?.toDouble();
    final edaM = (json['baseline_eda_mean'] as num?)?.toDouble();
    final tM = (json['baseline_temp_mean'] as num?)?.toDouble();
    final hrS = (json['baseline_hr_std'] as num?)?.toDouble();
    final edaS = (json['baseline_eda_std'] as num?)?.toDouble();
    final tS = (json['baseline_temp_std'] as num?)?.toDouble();
    if (!_isValidSignal(hrM) || !_isValidSignal(edaM) || !_isValidSignal(tM)) return false;

    _baseline = _BaselineStats(
      hrMean: hrM!,
      edaMean: edaM!,
      tempMean: tM!,
      hrStd: (hrS == null || !hrS.isFinite || hrS <= 0) ? 1.0 : hrS,
      edaStd: (edaS == null || !edaS.isFinite || edaS <= 0) ? 1.0 : edaS,
      tempStd: (tS == null || !tS.isFinite || tS <= 0) ? 1.0 : tS,
    );

    _calibWindows.clear();
    final count = ((json['windows'] as num?)?.toInt() ?? baselineWindows).clamp(0, 1000000);
    _calibrationValidCount = count;
    final seedCount = min(count, baselineWindows);
    for (int i = 0; i < seedCount; i++) {
      _calibWindows.add(
        _CalibWindow(hrMean: hrM, edaMean: edaM, tempMean: tM),
      );
    }
    return true;
  }

  bool get hasTrainedModel => _trainedLogistic != null || _trainedForest != null;
  bool get calibrationReady => hasTrainedModel && _baseline != null;
  bool get hasBaseline => _baseline != null;
  int get baselineCollected => _calibrationValidCount;
  int get baselineTarget => baselineWindows;
  int get currentWindowSamples => _points.length;
  int get windowTarget => windowSize;
  int get minSamplesForInference => _minInferenceSamples;

  void loadFlutterModel(Map<String, dynamic> json) {
    final type = (json['type'] ?? '').toString();
    if (type == 'random_forest_multiclass') {
      _trainedForest = _RandomForestModel.fromJson(json);
      _trainedLogistic = null;
      return;
    }

    _trainedLogistic = _LogisticModel.fromJson(json);
    _trainedForest = null;
  }

  StressInferenceResult? addSample({
    int? ts,
    double? bpmAvg,
    double? bpmMin,
    double? bpmMax,
    double? bpmStd,
    double? gsrAvg,
    double? gsrMin,
    double? gsrMax,
    double? gsrStd,
    double? tempAvg,
    double? tempMin,
    double? tempMax,
    double? tempStd,
  }) {
    if (bpmAvg == null || gsrAvg == null) return null;

    final effectiveTs = ts ?? (++_syntheticTs);
    _points.add(
      _SensorPoint(
        ts: effectiveTs.toDouble(),
        bpmAvg: bpmAvg,
        bpmMin: bpmMin ?? bpmAvg,
        bpmMax: bpmMax ?? bpmAvg,
        bpmStd: bpmStd ?? 0.0,
        gsrAvg: gsrAvg,
        gsrMin: gsrMin ?? gsrAvg,
        gsrMax: gsrMax ?? gsrAvg,
        gsrStd: gsrStd ?? 0.0,
        tempAvg: tempAvg,
        tempMin: tempMin ?? tempAvg,
        tempMax: tempMax ?? tempAvg,
        tempStd: tempStd ?? 0.0,
      ),
    );

    while (_points.length > windowSize) {
      _points.removeFirst();
    }

    _samplesSinceInference++;
    if (_points.length < _minInferenceSamples || _samplesSinceInference < stepSize) {
      return null;
    }
    _samplesSinceInference = 0;

    final canonical = _extractCanonicalFeatures(_points.toList(growable: false));

    if (_calibrationMode) {
      _collectCalibrationWindow(canonical);
    }

    final pred = _predict(canonical, _points.toList(growable: false));
    final calibrated = _calibrateProbability(canonical, pred.stressProbability);

    final smooth = _smoothedProb == null ? calibrated : (_smoothedProb! * 0.7 + calibrated * 0.3);
    _smoothedProb = smooth;

    final proxy = (smooth * 100.0).clamp(0.0, 100.0);
    final confidence = _deltaConfidence(canonical, smooth);
    final level = pred.levelOverride ?? _levelFromProbability(smooth);

    return StressInferenceResult(
      stressProbability: smooth,
      cortisolProxy: proxy,
      confidence: confidence,
      level: level,
      calibrationReady: calibrationReady,
    );
  }

  void _collectCalibrationWindow(Map<String, double> canonical) {
    final hr = canonical['bpm_avg'];
    final eda = canonical['gsr_avg'];
    final temp = canonical['temp_avg'];
    if (!_isValidSignal(hr) || !_isValidSignal(eda) || !_isValidSignal(temp)) return;
    if (hr! < 45 || hr > 190) return;
    if (temp! < 20 || temp > 45) return;

    _calibrationValidCount += 1;
    _calibWindows.add(_CalibWindow(hrMean: hr, edaMean: eda!, tempMean: temp));
    while (_calibWindows.length > baselineWindows) {
      _calibWindows.removeFirst();
    }

    _baseline = _BaselineStats.fromWindows(_calibWindows.toList(growable: false));
  }

  double _calibrateProbability(Map<String, double> canonical, double rawProb) {
    final b = _baseline;
    if (b == null) return rawProb;

    final hr = canonical['bpm_avg'] ?? b.hrMean;
    final eda = canonical['gsr_avg'] ?? b.edaMean;
    final temp = canonical['temp_avg'] ?? b.tempMean;

    final hrZ = (hr - b.hrMean) / max(1e-6, b.hrStd);
    final edaZ = (eda - b.edaMean) / max(1e-6, b.edaStd);
    final tempZ = (temp - b.tempMean) / max(1e-6, b.tempStd);

    final abnormal = (0.4 * hrZ.abs() + 0.4 * edaZ.abs() + 0.2 * tempZ.abs()).clamp(0.0, 3.0) / 3.0;
    final directionSupport = (0.5 * _sigmoid(hrZ) + 0.5 * _sigmoid(edaZ)).clamp(0.0, 1.0);

    var p = rawProb;

    if (p >= 0.60) {
      if (abnormal < 0.25 && directionSupport < 0.55) {
        p = (p - 0.10).clamp(0.0, 1.0);
      } else if (abnormal > 0.55 && directionSupport > 0.60) {
        p = (p + 0.07).clamp(0.0, 1.0);
      }
    } else if (p <= 0.40) {
      if (abnormal > 0.60 && directionSupport > 0.60) {
        p = (p + 0.06).clamp(0.0, 1.0);
      }
    } else {
      if (abnormal < 0.20) {
        p = (p - 0.04).clamp(0.0, 1.0);
      } else if (abnormal > 0.60 && directionSupport > 0.55) {
        p = (p + 0.04).clamp(0.0, 1.0);
      }
    }

    return p;
  }

  double _deltaConfidence(Map<String, double> canonical, double smoothedProb) {
    final b = _baseline;
    if (b == null) {
      return ((smoothedProb - 0.5).abs() * 2.0).clamp(0.0, 1.0);
    }

    final hr = canonical['bpm_avg'] ?? b.hrMean;
    final eda = canonical['gsr_avg'] ?? b.edaMean;
    final temp = canonical['temp_avg'] ?? b.tempMean;

    final hrZ = ((hr - b.hrMean) / max(1e-6, b.hrStd)).abs();
    final edaZ = ((eda - b.edaMean) / max(1e-6, b.edaStd)).abs();
    final tempZ = ((temp - b.tempMean) / max(1e-6, b.tempStd)).abs();

    double band(double z) {
      if (z < 0.5) return 0.20;
      if (z < 1.0) return 0.40;
      if (z < 1.5) return 0.60;
      if (z < 2.0) return 0.80;
      return 1.00;
    }

    final sensorConfidence = (0.4 * band(hrZ) + 0.4 * band(edaZ) + 0.2 * band(tempZ)).clamp(0.0, 1.0);
    final modelConfidence = ((smoothedProb - 0.5).abs() * 2.0).clamp(0.0, 1.0);
    return (0.7 * sensorConfidence + 0.3 * modelConfidence).clamp(0.0, 1.0);
  }

  double _sigmoid(double x) {
    final b = x.clamp(-8.0, 8.0);
    return 1.0 / (1.0 + exp(-b));
  }

  bool _isValidSignal(double? v) {
    if (v == null) return false;
    if (!v.isFinite) return false;
    return v > 0;
  }

  _ModelPrediction _predict(Map<String, double> canonicalFeatures, List<_SensorPoint> points) {
    if (_trainedForest != null) {
      final nurseFeatures = _extractNurseFeatures(points);
      return _trainedForest!.predict(nurseFeatures);
    }

    if (_trainedLogistic != null) {
      final adapted = _adaptFeatureUnits(canonicalFeatures);
      final prob = _trainedLogistic!.predictProbability(adapted);
      return _ModelPrediction(stressProbability: prob);
    }

    final adapted = _adaptFeatureUnits(canonicalFeatures);
    const weights = <String, double>{
      'bpm_avg': 0.15,
      'bpm_std': 0.10,
      'gsr_avg': 0.24,
      'gsr_std': 0.18,
      'gsr_slope': 0.14,
      'temp_avg': -0.07,
      'temp_slope': -0.05,
    };
    double logit = -0.15;
    weights.forEach((k, w) => logit += w * (adapted[k] ?? 0.0));
    final bounded = logit.clamp(-8.0, 8.0);
    final prob = 1.0 / (1.0 + exp(-bounded));
    return _ModelPrediction(stressProbability: prob);
  }

  StressLevel _levelFromProbability(double p) {
    if (p < 0.40) return StressLevel.low;
    if (p < 0.70) return StressLevel.medium;
    return StressLevel.high;
  }

  Map<String, double> _extractCanonicalFeatures(List<_SensorPoint> points) {
    final ts = points.map((p) => p.ts).toList(growable: false);
    final bpmAvg = points.map((p) => p.bpmAvg).toList(growable: false);
    final bpmMin = points.map((p) => p.bpmMin).toList(growable: false);
    final bpmMax = points.map((p) => p.bpmMax).toList(growable: false);
    final bpmStd = points.map((p) => p.bpmStd).toList(growable: false);

    final gsrAvg = points.map((p) => p.gsrAvg).toList(growable: false);
    final gsrMin = points.map((p) => p.gsrMin).toList(growable: false);
    final gsrMax = points.map((p) => p.gsrMax).toList(growable: false);
    final gsrStd = points.map((p) => p.gsrStd).toList(growable: false);

    final tempAvg = points.where((p) => p.tempAvg != null).map((p) => p.tempAvg!).toList(growable: false);
    final tempMin = points.where((p) => p.tempMin != null).map((p) => p.tempMin!).toList(growable: false);
    final tempMax = points.where((p) => p.tempMax != null).map((p) => p.tempMax!).toList(growable: false);
    final tempStd = points.where((p) => p.tempStd != null).map((p) => p.tempStd!).toList(growable: false);

    return {
      'bpm_avg': _mean(bpmAvg),
      'bpm_min': _mean(bpmMin),
      'bpm_max': _mean(bpmMax),
      'bpm_std': _mean(bpmStd),
      'hrv_rmssd': _rmssdFromBpm(bpmAvg),
      'hrv_sdnn': _std(bpmAvg, _mean(bpmAvg)),
      'gsr_avg': _mean(gsrAvg),
      'gsr_min': _mean(gsrMin),
      'gsr_max': _mean(gsrMax),
      'gsr_std': _mean(gsrStd),
      'gsr_slope': _slope(ts, gsrAvg),
      'temp_avg': tempAvg.isEmpty ? 0.0 : _mean(tempAvg),
      'temp_min': tempMin.isEmpty ? 0.0 : _mean(tempMin),
      'temp_max': tempMax.isEmpty ? 0.0 : _mean(tempMax),
      'temp_std': tempStd.isEmpty ? 0.0 : _mean(tempStd),
      'temp_slope': tempAvg.length < 2 ? 0.0 : _slope(ts.take(tempAvg.length).toList(), tempAvg),
    };
  }

  Map<String, double> _extractNurseFeatures(List<_SensorPoint> points) {
    final bpmSeries = points.map((p) => _normalizeBpmForNurse(p.bpmAvg)).toList(growable: false);
    final gsrSeries = points.map((p) => _normalizeGsrForNurse(p.gsrAvg)).toList(growable: false);
    final tempSeries = points
        .map((p) => _normalizeTempForNurse(p.tempAvg ?? p.tempMin ?? p.tempMax ?? 0.0))
        .toList(growable: false);

    double lagValue(List<double> s, int lag) {
      final idx = s.length - 1 - lag;
      if (idx >= 0) return s[idx];
      return s.isEmpty ? 0.0 : s.first;
    }

    final out = <String, double>{};

    for (int i = 0; i < 10; i++) {
      final lag = 10 - i;
      out[(30 - i).toString()] = lagValue(bpmSeries, lag);
      out[(20 - i).toString()] = lagValue(tempSeries, lag);
      out[(10 - i).toString()] = lagValue(gsrSeries, lag);
    }

    out['EDAR_Mean'] = _mean(gsrSeries);
    out['EDAR_Min'] = gsrSeries.isEmpty ? 0.0 : gsrSeries.reduce(min);
    out['EDAR_Max'] = gsrSeries.isEmpty ? 0.0 : gsrSeries.reduce(max);
    out['EDAR_Std'] = _std(gsrSeries, out['EDAR_Mean']!);

    out['HRR_Mean'] = _mean(bpmSeries);
    out['HRR_Min'] = bpmSeries.isEmpty ? 0.0 : bpmSeries.reduce(min);
    out['HRR_Max'] = bpmSeries.isEmpty ? 0.0 : bpmSeries.reduce(max);
    out['HRR_Std'] = _std(bpmSeries, out['HRR_Mean']!);

    out['TEMPR_Mean'] = _mean(tempSeries);
    out['TEMPR_Min'] = tempSeries.isEmpty ? 0.0 : tempSeries.reduce(min);
    out['TEMPR_Max'] = tempSeries.isEmpty ? 0.0 : tempSeries.reduce(max);
    out['TEMPR_Std'] = _std(tempSeries, out['TEMPR_Mean']!);

    return out;
  }

  double _normalizeBpmForNurse(double bpm) {
    return ((bpm - 40.0) / 140.0).clamp(0.0, 1.0);
  }

  double _normalizeGsrForNurse(double gsrRaw) {
    var g = gsrRaw;
    if (g > 50.0) g = g / 1000.0;
    final ln = log(g + 1.0);
    return (ln / log(6.0)).clamp(0.0, 1.0);
  }

  double _normalizeTempForNurse(double tempRaw) {
    var t = tempRaw;
    if (t > 80.0) t = t / 10.0;
    if (t > 80.0) t = t / 10.0;
    return ((t - 25.0) / 15.0).clamp(0.0, 1.0);
  }

  Map<String, double> _adaptFeatureUnits(Map<String, double> f) {
    final out = Map<String, double>.from(f);

    if ((out['gsr_avg'] ?? 0.0) > 50.0) {
      out['gsr_avg'] = (out['gsr_avg'] ?? 0.0) / 1000.0;
      out['gsr_min'] = (out['gsr_min'] ?? 0.0) / 1000.0;
      out['gsr_max'] = (out['gsr_max'] ?? 0.0) / 1000.0;
      out['gsr_std'] = (out['gsr_std'] ?? 0.0) / 1000.0;
      out['gsr_slope'] = (out['gsr_slope'] ?? 0.0) / 1000.0;
    }

    if ((out['temp_avg'] ?? 0.0) > 80.0) {
      out['temp_avg'] = (out['temp_avg'] ?? 0.0) / 10.0;
      out['temp_min'] = (out['temp_min'] ?? 0.0) / 10.0;
      out['temp_max'] = (out['temp_max'] ?? 0.0) / 10.0;
      out['temp_std'] = (out['temp_std'] ?? 0.0) / 10.0;
    }
    if ((out['temp_avg'] ?? 0.0) > 80.0) {
      out['temp_avg'] = (out['temp_avg'] ?? 0.0) / 10.0;
      out['temp_min'] = (out['temp_min'] ?? 0.0) / 10.0;
      out['temp_max'] = (out['temp_max'] ?? 0.0) / 10.0;
      out['temp_std'] = (out['temp_std'] ?? 0.0) / 10.0;
    }

    return out;
  }

  double _rmssdFromBpm(List<double> bpmVals) {
    if (bpmVals.length < 3) return 0.0;
    final rrMs = bpmVals.where((v) => v > 1e-6).map((v) => 60000.0 / v).toList(growable: false);
    if (rrMs.length < 3) return 0.0;

    double sum = 0.0;
    int count = 0;
    for (int i = 1; i < rrMs.length; i++) {
      final d = rrMs[i] - rrMs[i - 1];
      sum += d * d;
      count++;
    }
    if (count == 0) return 0.0;
    return sqrt(sum / count);
  }

  double _mean(List<double> values) {
    if (values.isEmpty) return 0.0;
    return values.reduce((a, b) => a + b) / values.length;
  }

  double _std(List<double> values, double mean) {
    if (values.length < 2) return 0.0;
    double sum = 0.0;
    for (final v in values) {
      final d = v - mean;
      sum += d * d;
    }
    return sqrt(sum / (values.length - 1));
  }

  double _slope(List<double> xs, List<double> ys) {
    if (xs.length != ys.length || xs.length < 2) return 0.0;

    final xMean = _mean(xs);
    final yMean = _mean(ys);

    double num = 0.0;
    double den = 0.0;
    for (int i = 0; i < xs.length; i++) {
      final xd = xs[i] - xMean;
      num += xd * (ys[i] - yMean);
      den += xd * xd;
    }
    if (den.abs() < 1e-9) return 0.0;
    return num / den;
  }
}

class _SensorPoint {
  final double ts;
  final double bpmAvg;
  final double bpmMin;
  final double bpmMax;
  final double bpmStd;
  final double gsrAvg;
  final double gsrMin;
  final double gsrMax;
  final double gsrStd;
  final double? tempAvg;
  final double? tempMin;
  final double? tempMax;
  final double? tempStd;

  const _SensorPoint({
    required this.ts,
    required this.bpmAvg,
    required this.bpmMin,
    required this.bpmMax,
    required this.bpmStd,
    required this.gsrAvg,
    required this.gsrMin,
    required this.gsrMax,
    required this.gsrStd,
    required this.tempAvg,
    required this.tempMin,
    required this.tempMax,
    required this.tempStd,
  });
}

class _CalibWindow {
  final double hrMean;
  final double edaMean;
  final double tempMean;

  const _CalibWindow({
    required this.hrMean,
    required this.edaMean,
    required this.tempMean,
  });
}

class _BaselineStats {
  final double hrMean;
  final double edaMean;
  final double tempMean;
  final double hrStd;
  final double edaStd;
  final double tempStd;

  const _BaselineStats({
    required this.hrMean,
    required this.edaMean,
    required this.tempMean,
    required this.hrStd,
    required this.edaStd,
    required this.tempStd,
  });

  factory _BaselineStats.fromWindows(List<_CalibWindow> ws) {
    if (ws.isEmpty) {
      return const _BaselineStats(
        hrMean: 0,
        edaMean: 0,
        tempMean: 0,
        hrStd: 1,
        edaStd: 1,
        tempStd: 1,
      );
    }

    double mean(List<double> v) => v.reduce((a, b) => a + b) / v.length;
    double std(List<double> v, double m) {
      if (v.length < 2) return 1.0;
      var s = 0.0;
      for (final x in v) {
        final d = x - m;
        s += d * d;
      }
      final out = sqrt(s / (v.length - 1));
      return (out <= 1e-6 || !out.isFinite) ? 1.0 : out;
    }

    final hrs = ws.map((e) => e.hrMean).toList(growable: false);
    final edas = ws.map((e) => e.edaMean).toList(growable: false);
    final temps = ws.map((e) => e.tempMean).toList(growable: false);

    final hrM = mean(hrs);
    final edaM = mean(edas);
    final tempM = mean(temps);

    return _BaselineStats(
      hrMean: hrM,
      edaMean: edaM,
      tempMean: tempM,
      hrStd: std(hrs, hrM),
      edaStd: std(edas, edaM),
      tempStd: std(temps, tempM),
    );
  }
}

class _ModelPrediction {
  final double stressProbability;
  final StressLevel? levelOverride;

  const _ModelPrediction({
    required this.stressProbability,
    this.levelOverride,
  });
}

class _LogisticModel {
  final List<String> features;
  final List<double> scalerMean;
  final List<double> scalerScale;
  final List<double> coef;
  final double intercept;

  _LogisticModel({
    required this.features,
    required this.scalerMean,
    required this.scalerScale,
    required this.coef,
    required this.intercept,
  });

  factory _LogisticModel.fromJson(Map<String, dynamic> json) {
    return _LogisticModel(
      features: (json['features'] as List).map((e) => e.toString()).toList(growable: false),
      scalerMean: (json['scaler_mean'] as List).map((e) => (e as num).toDouble()).toList(growable: false),
      scalerScale: (json['scaler_scale'] as List).map((e) => (e as num).toDouble()).toList(growable: false),
      coef: (json['coef'] as List).map((e) => (e as num).toDouble()).toList(growable: false),
      intercept: (json['intercept'] as num).toDouble(),
    );
  }

  double predictProbability(Map<String, double> inputFeatures) {
    double logit = intercept;
    for (int i = 0; i < features.length; i++) {
      final key = features[i];
      double raw = inputFeatures[key] ?? 0.0;
      final scale = (i < scalerScale.length && scalerScale[i].abs() > 1e-12) ? scalerScale[i] : 1.0;
      final mean = i < scalerMean.length ? scalerMean[i] : 0.0;

      if (key == 'hrv_rmssd' || key == 'hrv_sdnn') {
        raw = mean;
      }

      final z = ((raw - mean) / scale).clamp(-3.0, 3.0);
      final w = i < coef.length ? coef[i] : 0.0;
      logit += w * z;
    }

    final bounded = logit.clamp(-8.0, 8.0);
    return 1.0 / (1.0 + exp(-bounded));
  }
}

class _RandomForestModel {
  final List<int> classes;
  final List<String> features;
  final Map<String, double> featureMin;
  final Map<String, double> featureMax;
  final List<_TreeModel> trees;

  _RandomForestModel({
    required this.classes,
    required this.features,
    required this.featureMin,
    required this.featureMax,
    required this.trees,
  });

  factory _RandomForestModel.fromJson(Map<String, dynamic> json) {
    final treesJson = (json['trees'] as List).cast<Map<String, dynamic>>();
    return _RandomForestModel(
      classes: (json['classes'] as List).map((e) => (e as num).toInt()).toList(growable: false),
      features: (json['features'] as List).map((e) => e.toString()).toList(growable: false),
      featureMin: (json['feature_min'] as Map<String, dynamic>).map((k, v) => MapEntry(k, (v as num).toDouble())),
      featureMax: (json['feature_max'] as Map<String, dynamic>).map((k, v) => MapEntry(k, (v as num).toDouble())),
      trees: treesJson.map(_TreeModel.fromJson).toList(growable: false),
    );
  }

  _ModelPrediction predict(Map<String, double> inputFeatures) {
    final x = List<double>.filled(features.length, 0.0);
    for (int i = 0; i < features.length; i++) {
      final key = features[i];
      final raw = inputFeatures[key] ?? 0.0;
      final mn = featureMin[key] ?? 0.0;
      final mx = featureMax[key] ?? 1.0;
      final den = (mx - mn).abs() < 1e-9 ? 1.0 : (mx - mn);
      x[i] = ((raw - mn) / den).clamp(0.0, 1.0);
    }

    final probs = List<double>.filled(classes.length, 0.0);
    for (final t in trees) {
      final leafCounts = t.leafClassCounts(x);
      var sum = 0.0;
      for (final c in leafCounts) {
        sum += c;
      }
      if (sum <= 0) continue;
      for (int i = 0; i < probs.length && i < leafCounts.length; i++) {
        probs[i] += leafCounts[i] / sum;
      }
    }

    if (trees.isNotEmpty) {
      for (int i = 0; i < probs.length; i++) {
        probs[i] = probs[i] / trees.length;
      }
    }

    final idx1 = classes.indexOf(1);
    final idx2 = classes.indexOf(2);
    final p1 = idx1 >= 0 ? probs[idx1] : 0.0;
    final p2 = idx2 >= 0 ? probs[idx2] : 0.0;
    final stressProb = ((p1 + (2.0 * p2)) / 2.0).clamp(0.0, 1.0);

    var best = 0;
    for (int i = 1; i < probs.length; i++) {
      if (probs[i] > probs[best]) best = i;
    }
    final cls = classes.isNotEmpty ? classes[best] : 0;
    final level = cls <= 0 ? StressLevel.low : (cls == 1 ? StressLevel.medium : StressLevel.high);

    return _ModelPrediction(
      stressProbability: stressProb,
      levelOverride: level,
    );
  }
}

class _TreeModel {
  final List<int> childrenLeft;
  final List<int> childrenRight;
  final List<int> feature;
  final List<double> threshold;
  final List<List<double>> value;

  _TreeModel({
    required this.childrenLeft,
    required this.childrenRight,
    required this.feature,
    required this.threshold,
    required this.value,
  });

  factory _TreeModel.fromJson(Map<String, dynamic> json) {
    return _TreeModel(
      childrenLeft: (json['children_left'] as List).map((e) => (e as num).toInt()).toList(growable: false),
      childrenRight: (json['children_right'] as List).map((e) => (e as num).toInt()).toList(growable: false),
      feature: (json['feature'] as List).map((e) => (e as num).toInt()).toList(growable: false),
      threshold: (json['threshold'] as List).map((e) => (e as num).toDouble()).toList(growable: false),
      value: (json['value'] as List)
          .map((row) => (row as List).map((v) => (v as num).toDouble()).toList(growable: false))
          .toList(growable: false),
    );
  }

  List<double> leafClassCounts(List<double> x) {
    var node = 0;
    while (node >= 0 && node < childrenLeft.length) {
      final left = childrenLeft[node];
      final right = childrenRight[node];
      if (left < 0 || right < 0) {
        return node < value.length ? value[node] : const [1.0, 0.0, 0.0];
      }

      final fi = feature[node];
      final thr = threshold[node];
      final xv = (fi >= 0 && fi < x.length) ? x[fi] : 0.0;
      node = xv <= thr ? left : right;
    }
    return const [1.0, 0.0, 0.0];
  }
}
