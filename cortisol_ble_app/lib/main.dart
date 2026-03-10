// lib/main.dart
import 'dart:async';
import 'dart:convert';
import 'dart:io';
import 'dart:math';

import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_blue_plus/flutter_blue_plus.dart';
import 'package:cortisol_ble_app/ml/stress_engine.dart';
import 'package:path_provider/path_provider.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  runApp(const CortisolBleApp());
}

class CortisolBleApp extends StatelessWidget {
  const CortisolBleApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      title: "Cortisol BLE",
      debugShowCheckedModeBanner: false,
      theme: ThemeData(
        useMaterial3: true,
        colorSchemeSeed: const Color(0xFF3B82F6),
        brightness: Brightness.dark,

        // FIX 1: CardThemeData not CardTheme
        cardTheme: CardThemeData(
          elevation: 0,
          shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
        ),
      ),
      home: const BleHome(),
    );
  }
}

class BleHome extends StatefulWidget {
  const BleHome({super.key});

  @override
  State<BleHome> createState() => _BleHomeState();
}

enum SessionLabel { unlabeled, rest, stressTask, recovery }

extension SessionLabelX on SessionLabel {
  String get value {
    switch (this) {
      case SessionLabel.unlabeled:
        return "unlabeled";
      case SessionLabel.rest:
        return "rest";
      case SessionLabel.stressTask:
        return "stress_task";
      case SessionLabel.recovery:
        return "recovery";
    }
  }

  String get title {
    switch (this) {
      case SessionLabel.unlabeled:
        return "Unlabeled";
      case SessionLabel.rest:
        return "Rest";
      case SessionLabel.stressTask:
        return "Stress Task";
      case SessionLabel.recovery:
        return "Recovery";
    }
  }
}

class _BleHomeState extends State<BleHome> {
  final Guid knownCharUuid = Guid("abcd1234-5678-1234-5678-abcdef123456");
  final Guid heartbeatCharUuid = Guid("abcd1234-5678-1234-5678-abcdef123457");
  final Guid? knownServiceUuid = null;
  static const String _serviceChangedUuid = "00002a0500001000800000805f9b34fb";

  final Map<String, ScanResult> _scanByDeviceId = {};
  StreamSubscription<List<ScanResult>>? _scanSub;

  BluetoothDevice? _device;
  StreamSubscription<BluetoothConnectionState>? _connSub;

  BluetoothCharacteristic? _notifyChar;
  BluetoothCharacteristic? _heartbeatChar;
  StreamSubscription<List<int>>? _notifySub;
  StreamSubscription<List<int>>? _notifySubAlt;

  bool _scanning = false;
  bool _connecting = false;
  bool _reconnecting = false;
  bool _isConnected = false;
  int _tabIndex = 0;
  bool _mlModelLoaded = false;
  bool _resubscribing = false;
  DateTime? _lastNotifyAt;
  DateTime? _lastAutoReconnectAt;
  Timer? _notifyWatchdog;
  Timer? _autoReconnectTimer;
  Timer? _heartbeatTimer;
  int _heartbeatWriteFailures = 0;

  String _status = "Idle";
  String _parseStatus = "Waiting";
  String _raw = "";
  String _deviceNameFilter = "";
  String? _lastError;
  late final TextEditingController _filterController;

  final _assembler = JsonChunkAssembler();

  MetricGroup? _bpm;
  MetricGroup? _gsr;
  double? _temp;
  int? _ts;
  StressInferenceResult? _stressResult;
  String? _stressInputIssue;
  final StressEngine _stressEngine = StressEngine();

  final List<double> _bpmHistory = [];
  final List<double> _gsrHistory = [];
  final List<double> _tempHistory = [];
  final List<double> _stressHistory = [];
  final List<HistoryEntry> _history = [];
  ScanResult? _lastConnectedScan;
  Map<String, dynamic> _modelInfo = const {};
  Map<String, dynamic> _modelMetrics = const {};
  SessionLabel _sessionLabel = SessionLabel.unlabeled;
  File? _historyCsvFile;
  String? _historyCsvPath;
  int _loggedRows = 0;
  File? _calibrationFile;
  String? _lastCalibrationSignature;
  String _activeUserId = "default";
  late final TextEditingController _userIdController;
  bool _guidedCalibrationActive = false;
  bool _calibrationPromptShown = false;
  bool _showDeveloperTools = false;
  DateTime? _guidedCalibrationStartedAt;
  Timer? _calibrationTicker;
  static const Duration _minCalibrationDuration = Duration(minutes: 2);
  bool _stressMeasureActive = false;
  DateTime? _stressMeasureStartedAt;
  Timer? _stressMeasureTicker;
  final List<double> _measureScores = [];
  final List<double> _measureConfidences = [];
  int _measureValidSamples = 0;
  int _measureInvalidSamples = 0;
  String? _measureLiveIssue;
  _MeasureSummary? _lastMeasureSummary;
  int _calibrationInvalidSamples = 0;
  int? _lastProcessedTs;
  static const Duration _measureDuration = Duration(seconds: 60);
  static const int _measureMinValidSamples = 8;

  @override
  void initState() {
    super.initState();
    _filterController = TextEditingController(text: _deviceNameFilter);
    _userIdController = TextEditingController(text: _activeUserId);
    _loadMlModel();
    _loadModelMetadata();
    _initHistoryLogging();
    _initCalibrationStorage();
    _notifyWatchdog = Timer.periodic(const Duration(seconds: 3), (_) => _watchNotifyHealth());
    _autoReconnectTimer = Timer.periodic(const Duration(seconds: 10), (_) async {
      if (!mounted || !_connected || _connecting || _reconnecting || _resubscribing) return;
      await _silentReconnect();
    });
  }

  Future<void> _initHistoryLogging() async {
    try {
      final dir = await getApplicationDocumentsDirectory();
      final stamp = DateTime.now().toIso8601String().replaceAll(":", "-");
      final file = File("${dir.path}/stress_history_$stamp.csv");
      await file.writeAsString(
        "time_iso,ts,bpm_avg,gsr_avg,temp_avg,stress_prob,cortisol_proxy,stress_level,label,ml_loaded\n",
        mode: FileMode.write,
      );
      if (!mounted) return;
      setState(() {
        _historyCsvFile = file;
        _historyCsvPath = file.path;
        _loggedRows = 0;
      });
    } catch (e) {
      _setError("History logger init failed: $e");
    }
  }

  Future<void> _initCalibrationStorage() async {
    try {
      await _switchCalibrationUser(_activeUserId, showToast: false);
    } catch (e) {
      _setError("Calibration load failed: $e");
    }
  }

  Future<void> _switchCalibrationUser(String userId, {bool showToast = true}) async {
    final cleaned = userId.trim().isEmpty ? "default" : userId.trim();
    final dir = await getApplicationDocumentsDirectory();
    final file = File("${dir.path}/user_calibration_$cleaned.json");
    _calibrationFile = file;
    _activeUserId = cleaned;
    _userIdController.text = cleaned;
    _lastCalibrationSignature = null;
    _stressEngine.resetCalibration();
    if (await file.exists()) {
      final raw = await file.readAsString();
      final map = json.decode(raw) as Map<String, dynamic>;
      _stressEngine.loadCalibration(map);
    }
    if (mounted) {
      setState(() {});
    }
    if (showToast) {
      await _showToast("Active user: $cleaned");
    }
  }

  void _maybePromptCalibration() {
    if (!mounted || _calibrationPromptShown || !_connected) return;
    if (_stressEngine.hasBaseline) return;
    _calibrationPromptShown = true;
    WidgetsBinding.instance.addPostFrameCallback((_) async {
      if (!mounted) return;
      await showDialog<void>(
        context: context,
        barrierDismissible: true,
        builder: (ctx) {
          return AlertDialog(
            title: const Text("Please calibrate"),
            content: const Text(
              "For better personal accuracy, sit calmly for 2 to 5 minutes with minimal movement and normal breathing. Keep good sensor contact. Press Calibrate now to start.",
            ),
            actions: [
              TextButton(
                onPressed: () => Navigator.of(ctx).pop(),
                child: const Text("Later"),
              ),
              FilledButton(
                onPressed: () {
                  Navigator.of(ctx).pop();
                  unawaited(_startGuidedCalibrationWithUserPrompt());
                },
                child: const Text("Calibrate now"),
              ),
            ],
          );
        },
      );
    });
  }

  void _startGuidedCalibration() {
    if (!_connected) {
      unawaited(_showToast("Connect device before calibration"));
      return;
    }
    if (!mounted) return;
    setState(() {
      _guidedCalibrationActive = true;
      _sessionLabel = SessionLabel.rest;
      _tabIndex = 1; // Dashboard
      _guidedCalibrationStartedAt = DateTime.now();
      _calibrationInvalidSamples = 0;
    });
    _stressEngine.setCalibrationMode(true);
    _calibrationTicker?.cancel();
    _calibrationTicker = Timer.periodic(const Duration(seconds: 1), (_) {
      if (!mounted || !_guidedCalibrationActive) return;
      setState(() {});
    });
  }

  Future<void> _startGuidedCalibrationWithUserPrompt() async {
    final controller = TextEditingController(text: _activeUserId);
    final selected = await showDialog<String>(
      context: context,
      barrierDismissible: true,
      builder: (ctx) {
        return AlertDialog(
          title: const Text("Calibration user"),
          content: TextField(
            controller: controller,
            decoration: const InputDecoration(
              labelText: "User ID",
              hintText: "example user_01",
              border: OutlineInputBorder(),
            ),
          ),
          actions: [
            TextButton(
              onPressed: () => Navigator.of(ctx).pop(),
              child: const Text("Cancel"),
            ),
            FilledButton(
              onPressed: () => Navigator.of(ctx).pop(controller.text.trim()),
              child: const Text("Start"),
            ),
          ],
        );
      },
    );
    if (selected == null) return;
    await _switchCalibrationUser(selected);
    _startGuidedCalibration();
  }

  void _stopGuidedCalibration() {
    _stressEngine.setCalibrationMode(false);
    _calibrationTicker?.cancel();
    _calibrationTicker = null;
    if (!mounted) return;
    setState(() {
      _guidedCalibrationActive = false;
      _guidedCalibrationStartedAt = null;
    });
  }

  Future<void> _persistCalibrationIfNeeded() async {
    final f = _calibrationFile;
    if (f == null) return;
    final payload = _stressEngine.exportCalibration();
    if (payload == null) return;
    final signature = json.encode(payload);
    if (_lastCalibrationSignature == signature) return;
    _lastCalibrationSignature = signature;
    try {
      await f.writeAsString(signature, mode: FileMode.write);
    } catch (e) {
      _setError("Calibration save failed: $e");
    }
  }

  Future<void> _resetCalibration() async {
    _stressEngine.resetCalibration();
    _stressEngine.setCalibrationMode(false);
    _lastCalibrationSignature = null;
    final f = _calibrationFile;
    try {
      if (f != null && await f.exists()) {
        await f.delete();
      }
    } catch (_) {}
    if (!mounted) return;
    setState(() {
      _guidedCalibrationActive = false;
      _guidedCalibrationStartedAt = null;
      _calibrationInvalidSamples = 0;
    });
    await _showToast("Calibration reset");
  }

  Future<void> _loadMlModel() async {
    try {
      try {
        final nurseRaw = await rootBundle.loadString('assets/models/nurse_rf_model.json');
        final nurseJson = json.decode(nurseRaw) as Map<String, dynamic>;
        _stressEngine.loadFlutterModel(nurseJson);
        if (!mounted) return;
        setState(() => _mlModelLoaded = true);
        return;
      } catch (_) {
        // Fall back to previous logistic asset.
      }

      final raw = await rootBundle.loadString('assets/models/model_flutter.json');
      final jsonMap = json.decode(raw) as Map<String, dynamic>;
      _stressEngine.loadFlutterModel(jsonMap);
      if (!mounted) return;
      setState(() => _mlModelLoaded = true);
    } catch (e) {
      _setError('ML model load failed, using fallback engine: $e');
      if (!mounted) return;
      setState(() => _mlModelLoaded = false);
    }
  }

  Future<void> _loadModelMetadata() async {
    try {
      final infoRaw = await rootBundle.loadString('assets/models/model_info.json');
      final metricsRaw = await rootBundle.loadString('assets/models/metrics.json');
      if (!mounted) return;
      setState(() {
        _modelInfo = json.decode(infoRaw) as Map<String, dynamic>;
        _modelMetrics = json.decode(metricsRaw) as Map<String, dynamic>;
      });
    } catch (_) {
      // keep UI running even if metadata asset is missing
    }
  }

  @override
  void dispose() {
    _scanSub?.cancel();
    _connSub?.cancel();
    _notifySub?.cancel();
    _notifySubAlt?.cancel();
    _notifyWatchdog?.cancel();
    _autoReconnectTimer?.cancel();
    _heartbeatTimer?.cancel();
    _calibrationTicker?.cancel();
    _stressMeasureTicker?.cancel();
    _device?.disconnect();
    _filterController.dispose();
    _userIdController.dispose();
    super.dispose();
  }

  Duration get _guidedCalibrationElapsed {
    final started = _guidedCalibrationStartedAt;
    if (!_guidedCalibrationActive || started == null) return Duration.zero;
    return DateTime.now().difference(started);
  }

  Duration get _guidedCalibrationRemaining {
    final left = _minCalibrationDuration - _guidedCalibrationElapsed;
    return left.isNegative ? Duration.zero : left;
  }

  bool get _guidedCalibrationTimeDone => _guidedCalibrationElapsed >= _minCalibrationDuration;
  bool get _calibrationHasValidSignals =>
      _isValidSignal((_bpm ?? const MetricGroup()).avg) &&
      _isValidSignal((_gsr ?? const MetricGroup()).avg) &&
      _isValidSignal(_temp);
  Duration get _stressMeasureElapsed {
    final started = _stressMeasureStartedAt;
    if (!_stressMeasureActive || started == null) return Duration.zero;
    return DateTime.now().difference(started);
  }

  Duration get _stressMeasureRemaining {
    final left = _measureDuration - _stressMeasureElapsed;
    return left.isNegative ? Duration.zero : left;
  }

  double get _stressMeasureProgress {
    if (_measureDuration.inMilliseconds == 0) return 0;
    return (_stressMeasureElapsed.inMilliseconds / _measureDuration.inMilliseconds).clamp(0.0, 1.0);
  }

  String? _plausibilityIssue({double? bpmAvg, double? gsrAvg, double? tempAvg}) {
    if (!_isValidSignal(bpmAvg)) return "Heart rate not detected";
    if (!_isValidSignal(gsrAvg)) return "GSR not detected";
    if (!_isValidSignal(tempAvg)) return "Temperature not detected";
    if (bpmAvg! < 45 || bpmAvg > 190) {
      return "Heart rate out of range. Adjust finger sensor contact.";
    }
    if (tempAvg! < 20 || tempAvg > 45) {
      return "Temperature out of range. Check skin contact.";
    }
    return null;
  }

  void _startStressMeasurement() {
    if (!_connected) {
      unawaited(_showToast("Connect device before measuring stress"));
      return;
    }
    if (_stressMeasureActive) return;
    setState(() {
      _stressMeasureActive = true;
      _stressMeasureStartedAt = DateTime.now();
      _measureScores.clear();
      _measureConfidences.clear();
      _measureValidSamples = 0;
      _measureInvalidSamples = 0;
      _measureLiveIssue = null;
      _lastProcessedTs = null;
    });
    _stressMeasureTicker?.cancel();
    _stressMeasureTicker = Timer.periodic(const Duration(seconds: 1), (_) {
      if (!mounted || !_stressMeasureActive) return;
      if (_stressMeasureRemaining == Duration.zero) {
        _finalizeStressMeasurement();
        return;
      }
      setState(() {});
    });
  }

  void _cancelStressMeasurement() {
    _stressMeasureTicker?.cancel();
    _stressMeasureTicker = null;
    if (!mounted) return;
    setState(() {
      _stressMeasureActive = false;
      _stressMeasureStartedAt = null;
      _measureLiveIssue = "Measurement cancelled";
    });
  }

  void _finalizeStressMeasurement() {
    if (!_stressMeasureActive) return;
    _stressMeasureTicker?.cancel();
    _stressMeasureTicker = null;

    final enough = _measureValidSamples >= _measureMinValidSamples && _measureScores.isNotEmpty;
    _MeasureSummary? summary;
    if (enough) {
      final meanScore = _measureScores.reduce((a, b) => a + b) / _measureScores.length;
      final meanConfidence = _measureConfidences.isEmpty
          ? 0.0
          : _measureConfidences.reduce((a, b) => a + b) / _measureConfidences.length;
      final level = meanScore >= 0.67 ? "High" : (meanScore >= 0.34 ? "Medium" : "Low");
      summary = _MeasureSummary(
        score: meanScore,
        confidence: meanConfidence,
        level: level,
        validSamples: _measureValidSamples,
        invalidSamples: _measureInvalidSamples,
      );
    }

    HistoryEntry? measuredEntry;
    if (summary != null) {
      measuredEntry = HistoryEntry(
        when: DateTime.now(),
        ts: _ts,
        bpmAvg: _bpm?.avg,
        gsrAvg: _gsr?.avg,
        tempAvg: _temp,
        stressProb: summary.score,
        cortisolProxy: summary.score * 100.0,
        stressLevel: summary.level,
        label: _sessionLabel.value,
      );
    }

    if (!mounted) return;
    setState(() {
      _stressMeasureActive = false;
      _stressMeasureStartedAt = null;
      _lastMeasureSummary = summary;
      if (summary == null) {
        _measureLiveIssue = "Not enough valid samples. Re-measure with better sensor contact.";
      } else {
        _measureLiveIssue = null;
        _history.add(measuredEntry!);
        if (_history.length > 300) _history.removeAt(0);
      }
    });
    if (measuredEntry != null) {
      unawaited(_appendHistoryLog(measuredEntry));
    }
    if (summary != null) {
      unawaited(_sendStressResultToDevice(summary));
    }

    showDialog<void>(
      context: context,
      builder: (ctx) => AlertDialog(
        title: const Text("Stress measurement result"),
        content: summary == null
            ? Text("Measurement ended but valid samples were too low.\n\nValid: $_measureValidSamples\nInvalid: $_measureInvalidSamples")
            : Text(
                "Final stress level: ${summary.level}\n"
                "Stress score: ${summary.score.toStringAsFixed(3)}\n"
                "Confidence: ${(summary.confidence * 100).toStringAsFixed(0)}%\n"
                "Cortisol proxy: ${(summary.score * 100).toStringAsFixed(1)}\n"
                "Valid samples: ${summary.validSamples}\n"
                "Invalid samples: ${summary.invalidSamples}",
              ),
        actions: [
          TextButton(
            onPressed: () => Navigator.of(ctx).pop(),
            child: const Text("Close"),
          ),
        ],
      ),
    );
  }

  String _fmtDuration(Duration d) {
    final total = d.inSeconds < 0 ? 0 : d.inSeconds;
    final mm = (total ~/ 60).toString().padLeft(2, '0');
    final ss = (total % 60).toString().padLeft(2, '0');
    return "$mm:$ss";
  }

  String _fmtMinuteProgress(Duration elapsed, Duration target) {
    final e = (elapsed.inSeconds / 60.0).clamp(0.0, 999.0);
    final t = max(0.1, target.inSeconds / 60.0);
    return "${e.toStringAsFixed(1)}/${t.toStringAsFixed(1)} min";
  }

  void _openStressDetailsPage() {
    Navigator.of(context).push(
      MaterialPageRoute(
        builder: (_) => _StressDetailsPage(
          measuredSummary: _lastMeasureSummary,
          stressResult: _stressResult,
          stressInputIssue: _stressInputIssue,
          mlModelLoaded: _mlModelLoaded,
          calibrationReady: _stressEngine.calibrationReady,
          calibrationSamples: _stressEngine.baselineCollected,
          calibrationSampleMin: _stressEngine.baselineTarget,
          calibrationElapsedText: _fmtMinuteProgress(_guidedCalibrationElapsed, _minCalibrationDuration),
          calibrationRemainingText: _fmtDuration(_guidedCalibrationRemaining),
          inferenceWindowText: "${_stressEngine.currentWindowSamples}/${_stressEngine.windowTarget}",
          guidedCalibrationActive: _guidedCalibrationActive,
        ),
      ),
    );
  }

  void _openGraphPage({
    required String title,
    required String unit,
    required List<double> data,
  }) {
    Navigator.of(context).push(
      MaterialPageRoute(
        builder: (_) => _GraphDetailPage(
          title: title,
          unit: unit,
          data: List<double>.from(data),
        ),
      ),
    );
  }

  Future<void> _watchNotifyHealth() async {
    if (!mounted || !_connected || _notifyChar == null || _connecting || _reconnecting || _resubscribing) {
      return;
    }
    final last = _lastNotifyAt;
    if (last == null) return;
    final now = DateTime.now();
    final stalled = now.difference(last).inSeconds >= 8;
    if (!stalled) return;
    await _resubscribeNotify();

    // If data is still stale after resubscribe, mimic manual reconnect button.
    final currentLast = _lastNotifyAt;
    final stillStale = currentLast == null || now.difference(currentLast).inSeconds >= 8;
    if (!stillStale) return;
    final canReconnect = _lastAutoReconnectAt == null || now.difference(_lastAutoReconnectAt!).inSeconds >= 15;
    if (!canReconnect) return;
    _lastAutoReconnectAt = now;
    if (mounted) {
      setState(() => _parseStatus = "Auto reconnecting");
    }
    await _silentReconnect();
  }

  Future<void> _resubscribeNotify() async {
    final char = _notifyChar;
    if (char == null || _resubscribing) return;
    _resubscribing = true;
    try {
      await _notifySub?.cancel();
      await _notifySubAlt?.cancel();
      _notifySub = null;
      _notifySubAlt = null;
      try {
        await char.setNotifyValue(false);
      } catch (_) {}
      await Future.delayed(const Duration(milliseconds: 150));
      final ok = await _enableNotifyWithRetry(char);
      if (!ok) return;
      _attachNotifyStreams(char);
      _lastNotifyAt = DateTime.now();
      if (mounted) {
        setState(() {
          _parseStatus = "Resubscribed";
        });
      }
    } finally {
      _resubscribing = false;
    }
  }

  void _attachNotifyStreams(BluetoothCharacteristic target) {
    _notifySub = target.onValueReceived.listen((bytes) {
      if (!mounted || bytes.isEmpty) return;
      _onIncomingBytes(bytes);
    }, onError: (e) {
      _setError("Notify stream error: $e");
    });
    _notifySubAlt = target.lastValueStream.listen((bytes) {
      if (!mounted || bytes.isEmpty) return;
      _onIncomingBytes(bytes);
    }, onError: (e) {
      _setError("Notify stream(lastValue) error: $e");
    });
  }

  String _normGuid(Guid g) => _normGuidText(g.str);
  String _normGuidText(String value) {
    final s = value.toLowerCase().replaceAll("-", "");
    if (s.length == 4) return "0000${s}00001000800000805f9b34fb";
    if (s.length == 8) return "${s}00001000800000805f9b34fb";
    return s;
  }
  bool _isServiceChangedChar(BluetoothCharacteristic c) => _normGuid(c.uuid) == _serviceChangedUuid;
  bool get _connected => _isConnected;

  bool _matchesFilter(ScanResult r) {
    final f = _deviceNameFilter.trim().toLowerCase();
    if (f.isEmpty) return true;
    final name = r.device.platformName.toLowerCase();
    final advName = r.advertisementData.advName.toLowerCase();
    return name.contains(f) || advName.contains(f);
  }

  void _applyFilterToExistingResults() {
    final toRemove = <String>[];
    _scanByDeviceId.forEach((id, result) {
      if (!_matchesFilter(result)) {
        toRemove.add(id);
      }
    });
    for (final id in toRemove) {
      _scanByDeviceId.remove(id);
    }
  }

  void _setError(String message) {
    if (!mounted) return;
    setState(() => _lastError = message);
  }

  Future<void> _showToast(String message) async {
    if (!mounted) return;
    ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text(message)));
  }

  Future<void> _appendHistoryLog(HistoryEntry entry) async {
    final f = _historyCsvFile;
    if (f == null) return;
    final row = "${[
      entry.when.toIso8601String(),
      "${entry.ts ?? ""}",
      _csvNum(entry.bpmAvg),
      _csvNum(entry.gsrAvg),
      _csvNum(entry.tempAvg),
      entry.stressProb.toStringAsFixed(6),
      entry.cortisolProxy.toStringAsFixed(3),
      entry.stressLevel,
      entry.label,
      _mlModelLoaded ? "1" : "0",
    ].join(",")}\n";
    try {
      await f.writeAsString(row, mode: FileMode.append);
      if (mounted) {
        setState(() => _loggedRows += 1);
      }
    } catch (e) {
      _setError("History log write failed: $e");
    }
  }

  String _csvNum(double? v) => v == null ? "" : v.toStringAsFixed(4);

  Future<void> _copyHistoryCsvToClipboard() async {
    final f = _historyCsvFile;
    if (f == null) {
      await _showToast("History file not ready");
      return;
    }
    try {
      final content = await f.readAsString();
      await Clipboard.setData(ClipboardData(text: content));
      await _showToast("History CSV copied to clipboard");
    } catch (e) {
      _setError("CSV export failed: $e");
    }
  }

  Future<void> _startScan() async {
    if (_scanning) return;

    setState(() {
      _scanByDeviceId.clear();
      _scanning = true;
      _status = "Scanning";
    });

    try {
      await FlutterBluePlus.stopScan();
    } catch (_) {}

    _scanSub?.cancel();
    _scanSub = FlutterBluePlus.scanResults.listen((results) {
      bool changed = false;
      for (final r in results) {
        if (!_matchesFilter(r)) continue;
        final id = r.device.remoteId.str;
        final prev = _scanByDeviceId[id];
        if (prev == null || r.rssi > prev.rssi) {
          _scanByDeviceId[id] = r;
          changed = true;
        }
      }
      if (changed) setState(() {});
    });
    try {
      await FlutterBluePlus.startScan(
        timeout: const Duration(seconds: 8),
        androidScanMode: AndroidScanMode.lowLatency,
      );
    } catch (e) {
      _setError("Scan failed: $e");
    }

    setState(() {
      _scanning = false;
      _status = "Scan complete";
    });
  }

  Future<void> _stopScan() async {
    try {
      await FlutterBluePlus.stopScan();
    } catch (_) {}
    await _scanSub?.cancel();
    _scanSub = null;
    setState(() {
      _scanning = false;
      _status = "Scan stopped";
    });
  }

  Future<void> _disconnect() async {
    final d = _device;
    if (d == null) return;
    if (_stressMeasureActive) {
      _cancelStressMeasurement();
      unawaited(_showToast("Stress measurement stopped: device disconnected"));
    }
    if (_guidedCalibrationActive) {
      _stopGuidedCalibration();
      unawaited(_showToast("Calibration stopped: device disconnected"));
    }

    await _notifySub?.cancel();
    await _notifySubAlt?.cancel();
    _notifySub = null;
    _notifySubAlt = null;
    _heartbeatTimer?.cancel();
    _heartbeatTimer = null;
    _heartbeatChar = null;

    try {
      if (_notifyChar != null) {
        try {
          await _notifyChar!.setNotifyValue(false);
        } catch (_) {}
      }
    } catch (_) {}

    _notifyChar = null;
    _lastNotifyAt = null;

    try {
      await d.disconnect();
    } catch (_) {}

    setState(() {
      _device = null;
      _connecting = false;
      _reconnecting = false;
      _isConnected = false;
      _status = "Disconnected";
    });
  }

  Future<void> _resetSensorSession() async {
    final hb = _heartbeatChar;
    if (hb == null || !_connected) {
      await _showToast("Reset unavailable. Connect first.");
      return;
    }
    try {
      await _writeHeartbeat("RESET");
    } catch (_) {}
    await _showToast("Reset command sent. Sensor should be reconnectable shortly.");
    await _disconnect();
  }

  Future<void> _writeHeartbeat(String payload) async {
    final hb = _heartbeatChar;
    if (hb == null) return;
    final bytes = utf8.encode(payload);
    final preferNoResp = hb.properties.writeWithoutResponse;
    final firstMode = preferNoResp;
    try {
      await hb.write(bytes, withoutResponse: firstMode);
      _heartbeatWriteFailures = 0;
      return;
    } catch (_) {
      // Retry once using the opposite write mode.
    }
    try {
      await hb.write(bytes, withoutResponse: !firstMode);
      _heartbeatWriteFailures = 0;
    } catch (e) {
      _heartbeatWriteFailures += 1;
      if (_heartbeatWriteFailures >= 3) {
        _setError("Heartbeat write failed repeatedly: $e");
      }
    }
  }

  Future<void> _sendStressResultToDevice(_MeasureSummary summary) async {
    if (!_connected) return;
    final safeLevel = summary.level.replaceAll("|", "/").trim();
    final payload =
        "RESULT|$safeLevel|${summary.score.toStringAsFixed(3)}|${summary.confidence.toStringAsFixed(3)}";
    await _writeHeartbeat(payload);
  }

  void _startHeartbeat() {
    _heartbeatTimer?.cancel();
    _heartbeatTimer = Timer.periodic(const Duration(seconds: 5), (_) async {
      if (!_connected || _connecting || _reconnecting) return;
      final hb = _heartbeatChar;
      if (hb == null) return;
      await _writeHeartbeat("HB");
    });
  }

  Future<void> _reconnect() async {
    if (_reconnecting || _connecting) return;
    final target = _lastConnectedScan;
    if (target == null) {
      _setError("No previous device to reconnect.");
      return;
    }
    setState(() => _reconnecting = true);
    await _connectTo(target, resetData: false);
    if (mounted) {
      setState(() => _reconnecting = false);
    }
  }

  Future<void> _silentReconnect() async {
    if (_connecting || _reconnecting || _resubscribing) return;
    final target = _lastConnectedScan;
    if (target == null) return;
    await _connectTo(target, resetData: false, silentReconnect: true);
  }

  Future<void> _connectTo(ScanResult r, {bool resetData = true, bool silentReconnect = false}) async {
    if (_connecting) return;

    await _stopScan();

    setState(() {
      _connecting = true;
      _isConnected = false;
      if (!silentReconnect) _status = "Connecting";
      _lastError = null;
      if (resetData) {
        _raw = "";
        _parseStatus = "Waiting";
        _bpm = null;
        _gsr = null;
        _temp = null;
        _ts = null;
        _stressResult = null;
        _bpmHistory.clear();
        _gsrHistory.clear();
        _stressHistory.clear();
        _assembler.reset();
        _stressEngine.reset();
      }
    });

    final d = r.device;
    _lastConnectedScan = r;
    _lastNotifyAt = null;

    await _notifySub?.cancel();
    await _notifySubAlt?.cancel();
    _notifySub = null;
    _notifySubAlt = null;
    _notifyChar = null;
    _heartbeatChar = null;
    _heartbeatTimer?.cancel();
    _heartbeatTimer = null;
    await _connSub?.cancel();
    _connSub = null;

    _device = d;

    _connSub = d.connectionState.listen((s) {
      if (!mounted) return;
      setState(() {
        if (!silentReconnect) {
          _status = "Connection: ${s.name}";
        }
        _isConnected = s == BluetoothConnectionState.connected;
      });
      if (s == BluetoothConnectionState.disconnected) {
        if (_stressMeasureActive) {
          _cancelStressMeasurement();
          unawaited(_showToast("Stress measurement stopped: device disconnected"));
        }
        if (_guidedCalibrationActive) {
          _stopGuidedCalibration();
          unawaited(_showToast("Calibration stopped: device disconnected"));
        }
        _notifySub?.cancel();
        _notifySubAlt?.cancel();
        _notifySub = null;
        _notifySubAlt = null;
        _notifyChar = null;
        _heartbeatChar = null;
        _heartbeatTimer?.cancel();
        _heartbeatTimer = null;
      }
    });

    try {
      await d.connect(
        timeout: const Duration(seconds: 12),
        autoConnect: false,
        license: License.free,
      );
    } catch (e) {
      final msg = e.toString();
      if (!msg.contains("already connected")) {
        _setError("Connect failed: $e");
      }
    }

    await Future.delayed(const Duration(milliseconds: 400));

    try {
      await d.requestMtu(185);
    } catch (_) {}

    List<BluetoothService> services = await _discoverServicesWithRetry(d);
    if (services.isEmpty) {
      setState(() {
        _connecting = false;
        _status = "Discover services failed";
      });
      _setError("No services discovered.");
      return;
    }

    BluetoothCharacteristic? target;

    for (final s in services) {
      final serviceOk = knownServiceUuid == null || _normGuid(s.uuid) == _normGuid(knownServiceUuid!);
      if (!serviceOk) continue;

      for (final c in s.characteristics) {
        if (_isServiceChangedChar(c)) continue;
        if (_normGuid(c.uuid) == _normGuid(knownCharUuid)) {
          target = c;
          break;
        }
      }
      if (target != null) break;
    }

    target ??= _pickBestNotifiable(services);

    if (target == null) {
      setState(() {
        _connecting = false;
        _status = "No notifiable characteristic found";
      });
      return;
    }

    _notifyChar = target;
    _heartbeatChar = _findHeartbeatCharacteristic(services);
    _heartbeatWriteFailures = 0;
    if (_heartbeatChar == null) {
      _setError("Heartbeat characteristic not found. Remove old bond/app cache and reconnect.");
    }

    final notifyOk = await _enableNotifyWithRetry(target);
    if (!notifyOk) {
      setState(() {
        _connecting = false;
        _status = "Enable notify failed";
      });
      _setError("Could not enable notifications.");
      return;
    }

    await _notifySub?.cancel();
    await _notifySubAlt?.cancel();
    _attachNotifyStreams(target);
    _lastNotifyAt = DateTime.now();
    _startHeartbeat();
    unawaited(_writeHeartbeat("HB"));

    // Optional initial read
    try {
      final v = await target.read();
      if (v.isNotEmpty) {
        _onIncomingBytes(v);
      }
    } catch (_) {
      // some devices do not support reads on a notify-only characteristic
    }

    setState(() {
      _connecting = false;
      _isConnected = true;
      if (!silentReconnect) _status = "Connected";
      _parseStatus = "Listening";
    });
    _maybePromptCalibration();
  }

  BluetoothCharacteristic? _findHeartbeatCharacteristic(List<BluetoothService> services) {
    for (final s in services) {
      for (final c in s.characteristics) {
        if (_normGuid(c.uuid) != _normGuid(heartbeatCharUuid)) continue;
        if (c.properties.write || c.properties.writeWithoutResponse) return c;
      }
    }
    return null;
  }

  Future<List<BluetoothService>> _discoverServicesWithRetry(BluetoothDevice d) async {
    for (int attempt = 0; attempt < 2; attempt++) {
      try {
        final services = await d.discoverServices();
        if (services.isNotEmpty) return services;
      } catch (_) {
        // retry once
      }
      await Future.delayed(const Duration(milliseconds: 300));
    }
    return const [];
  }

  Future<bool> _enableNotifyWithRetry(BluetoothCharacteristic c) async {
    for (int attempt = 0; attempt < 2; attempt++) {
      try {
        await c.setNotifyValue(true);
        return true;
      } catch (_) {
        await Future.delayed(const Duration(milliseconds: 250));
      }
    }
    return false;
  }

  void _onIncomingBytes(List<int> bytes) {
    final chunk = utf8.decode(bytes, allowMalformed: true);
    if (chunk.isEmpty) return;
    _lastNotifyAt = DateTime.now();

    setState(() {
      _raw += chunk;
      if (_raw.length > 6000) {
        _raw = _raw.substring(_raw.length - 6000);
      }
    });

    final objects = _assembler.push(chunk);
    if (objects.isEmpty) {
      setState(() {
        _parseStatus = _assembler.pendingBytes > 0
            ? "Buffering (${_assembler.pendingBytes} chars)"
            : "Listening";
      });
      return;
    }

    for (final obj in objects) {
      _processJson(obj);
    }
  }

  BluetoothCharacteristic? _pickBestNotifiable(List<BluetoothService> services) {
    BluetoothCharacteristic? best;
    int bestScore = -99999;
    for (final s in services) {
      for (final c in s.characteristics) {
        final canNotify = c.properties.notify || c.properties.indicate;
        if (!canNotify) continue;
        if (_isServiceChangedChar(c)) continue;

        int score = 0;
        if (c.properties.notify) score += 20;
        if (c.properties.indicate) score += 10;
        if (knownServiceUuid != null && _normGuid(s.uuid) == _normGuid(knownServiceUuid!)) {
          score += 5;
        }
        if (score > bestScore) {
          best = c;
          bestScore = score;
        }
      }
    }
    return best;
  }

  void _processJson(Map<String, dynamic> obj) {
    int? ts;
    final tsRaw = obj["ts"] ?? obj["TS"] ?? obj["t"];
    if (tsRaw is num) ts = tsRaw.toInt();
    if (tsRaw is String) ts = int.tryParse(tsRaw);

    // Same BLE packet can arrive from both notify streams; dedupe by timestamp.
    if (ts != null && ts == _lastProcessedTs) {
      return;
    }

    MetricGroup? bpm;
    MetricGroup? gsr;
    MetricGroup? tempGroup;
    double? temp;

    final bpmObj = obj["BPM"] ?? obj["bpm"] ?? obj["b"];
    if (bpmObj is Map<String, dynamic>) {
      bpm = MetricGroup.fromMap(bpmObj);
    } else if (bpmObj is Map) {
      bpm = MetricGroup.fromMap(bpmObj.cast<String, dynamic>());
    }

    final gsrObj = obj["GSR"] ?? obj["gsr"] ?? obj["g"];
    if (gsrObj is Map<String, dynamic>) {
      gsr = MetricGroup.fromMap(gsrObj);
    } else if (gsrObj is Map) {
      gsr = MetricGroup.fromMap(gsrObj.cast<String, dynamic>());
    }

    final tempObj = obj["Temp"] ?? obj["TEMP"] ?? obj["temp"] ?? obj["skinTemp"] ?? obj["temperature"] ?? obj["tc"];
    if (tempObj is Map<String, dynamic>) {
      tempGroup = MetricGroup.fromMap(tempObj);
      temp = tempGroup.avg;
    } else if (tempObj is Map) {
      tempGroup = MetricGroup.fromMap(tempObj.cast<String, dynamic>());
      temp = tempGroup.avg;
    } else if (tempObj is num) {
      temp = tempObj.toDouble();
    } else if (tempObj is String) {
      temp = double.tryParse(tempObj);
    }

    // Device sometimes streams temperature in deci- or centi-degrees.
    if (temp != null && temp > 80) {
      temp = temp / 10.0;
      if (temp > 80) {
        temp = temp / 10.0;
      }
    }

    if (ts == null && bpm == null && gsr == null && temp == null) {
      setState(() => _parseStatus = "Parsed but no fields");
      return;
    }

    final bpmNow = bpm ?? _bpm;
    final gsrNow = gsr ?? _gsr;
    final tempAvgNow = temp ?? _temp;
    final tsVal = ts ?? _ts;
    final bpmValid = _isValidSignal(bpmNow?.avg);
    final gsrValid = _isValidSignal(gsrNow?.avg);
    final tempValid = _isValidSignal(tempAvgNow);

    String? stressIssue;
    if (!bpmValid) {
      stressIssue = "Stress requires valid heart rate";
    } else if (!gsrValid) {
      stressIssue = "Stress requires valid GSR";
    } else if (!tempValid) {
      stressIssue = "Stress requires valid temperature";
    } else {
      stressIssue = _plausibilityIssue(
        bpmAvg: bpmNow?.avg,
        gsrAvg: gsrNow?.avg,
        tempAvg: tempAvgNow,
      );
    }

    StressInferenceResult? inference;
    if (stressIssue == null) {
      inference = _stressEngine.addSample(
        ts: tsVal,
        bpmAvg: bpmNow?.avg,
        bpmMin: bpmNow?.min,
        bpmMax: bpmNow?.max,
        bpmStd: bpmNow?.std,
        gsrAvg: gsrNow?.avg,
        gsrMin: gsrNow?.min,
        gsrMax: gsrNow?.max,
        gsrStd: gsrNow?.std,
        tempAvg: tempAvgNow,
        tempMin: tempGroup?.min ?? tempAvgNow,
        tempMax: tempGroup?.max ?? tempAvgNow,
        tempStd: tempGroup?.std ?? 0.0,
      );
    }

    bool finalizeMeasure = false;
    setState(() {
      if (ts != null) {
        _lastProcessedTs = ts;
      }
      _ts = ts ?? _ts;
      _bpm = bpm ?? _bpm;
      _gsr = gsr ?? _gsr;
      _temp = temp ?? _temp;
      _stressInputIssue = stressIssue;
      if (inference != null) {
        _stressResult = inference;
        _stressHistory.add(inference.stressProbability);
        if (_stressHistory.length > 60) _stressHistory.removeAt(0);
      } else if (stressIssue != null) {
        _stressResult = null;
      }

      if (bpm?.avg != null) {
        _bpmHistory.add(bpm!.avg!);
        if (_bpmHistory.length > 30) _bpmHistory.removeAt(0);
      }
      if (gsr?.avg != null) {
        _gsrHistory.add(gsr!.avg!);
        if (_gsrHistory.length > 30) _gsrHistory.removeAt(0);
      }
      if (temp != null && temp.isFinite && temp > 0) {
        _tempHistory.add(temp);
        if (_tempHistory.length > 30) _tempHistory.removeAt(0);
      }

      if (_stressMeasureActive) {
        if (inference != null && stressIssue == null) {
          _measureScores.add(inference.stressProbability);
          _measureConfidences.add(inference.confidence);
          _measureValidSamples += 1;
          _measureLiveIssue = null;
        } else {
          _measureInvalidSamples += 1;
          _measureLiveIssue = stressIssue ?? "Waiting for enough window samples";
        }
        if (_stressMeasureRemaining == Duration.zero) {
          finalizeMeasure = true;
        }
      }
      if (_guidedCalibrationActive && stressIssue != null) {
        _calibrationInvalidSamples += 1;
      }

      _parseStatus = "OK";
    });
    unawaited(_persistCalibrationIfNeeded());

    if (_guidedCalibrationActive &&
        _stressEngine.baselineCollected >= _stressEngine.baselineTarget &&
        _guidedCalibrationTimeDone) {
      _stopGuidedCalibration();
      unawaited(_showToast("Calibration complete"));
    }
    if (finalizeMeasure) {
      _finalizeStressMeasurement();
    }
  }

  List<ScanResult> get _scanResultsSorted {
    final list = _scanByDeviceId.values.toList();
    list.sort((a, b) => b.rssi.compareTo(a.rssi));
    return list;
  }

  bool _isValidSignal(double? v) {
    if (v == null) return false;
    if (!v.isFinite) return false;
    return v > 0;
  }

  void _openHistoryPage() {
    Navigator.of(context).push(
      MaterialPageRoute(
        builder: (_) => _HistoryPage(
          entries: _history,
          csvPath: _historyCsvPath,
          loggedRows: _loggedRows,
          onCopyCsv: _copyHistoryCsvToClipboard,
        ),
      ),
    );
  }

  Widget _buildConnectionTab(String? connectedName) {
    final strongest = _scanResultsSorted.isEmpty ? null : _scanResultsSorted.first.rssi;
    return RefreshIndicator(
      onRefresh: _startScan,
      child: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          Card(
            child: Container(
              padding: const EdgeInsets.all(14),
              decoration: BoxDecoration(
                borderRadius: BorderRadius.circular(12),
                gradient: LinearGradient(
                  colors: [
                    Theme.of(context).colorScheme.primary.withValues(alpha: 0.20),
                    Theme.of(context).colorScheme.tertiary.withValues(alpha: 0.14),
                  ],
                  begin: Alignment.topLeft,
                  end: Alignment.bottomRight,
                ),
              ),
              child: Wrap(
                spacing: 8,
                runSpacing: 8,
                children: [
                  _MiniPill(text: _connected ? "Connected" : "Disconnected"),
                  _MiniPill(text: "Devices ${_scanResultsSorted.length}"),
                  _MiniPill(text: "Best RSSI ${strongest ?? "N/A"}"),
                  _MiniPill(text: "Parse $_parseStatus"),
                ],
              ),
            ),
          ),
          const SizedBox(height: 12),
          if (_lastError != null) ...[
            MaterialBanner(
              content: Text(_lastError!),
              leading: const Icon(Icons.error_outline),
              actions: [
                TextButton(
                  onPressed: () => setState(() => _lastError = null),
                  child: const Text("Dismiss"),
                ),
              ],
            ),
            const SizedBox(height: 12),
          ],
          _TopActions(
            scanning: _scanning,
            connecting: _connecting,
            connected: _connected,
            canReconnectLast: !_connected && _lastConnectedScan != null && !_reconnecting,
            onAutoFilterEsp32: () {
              const target = "ESP32_HealthMonitor";
              setState(() {
                _deviceNameFilter = target;
                _filterController.text = target;
                _applyFilterToExistingResults();
              });
            },
            connectedName: connectedName,
            parseStatus: _parseStatus,
            mlModelLoaded: _mlModelLoaded,
            filterController: _filterController,
            onFilterChanged: (value) {
              setState(() {
                _deviceNameFilter = value;
                _applyFilterToExistingResults();
              });
            },
            onScan: _startScan,
            onStopScan: _stopScan,
            onDisconnect: _disconnect,
            onReconnect: _reconnect,
            onResetSession: _resetSensorSession,
          ),
          const SizedBox(height: 12),
          _CardSection(
            title: "Nearby devices",
            subtitle: "Tap a device to connect. Pull down to rescan.",
            child: _scanResultsSorted.isEmpty
                ? _EmptyState(
                    text: _scanning ? "Scanning..." : "No devices yet. Tap Scan.",
                  )
                : Column(
                    children: _scanResultsSorted.map((r) {
                      final name = r.device.platformName.isNotEmpty ? r.device.platformName : "(no name)";
                      final id = r.device.remoteId.str;
                      return _DeviceTile(
                        name: name,
                        id: id,
                        rssi: r.rssi,
                        onTap: () => _connectTo(r),
                      );
                    }).toList(),
                  ),
          ),
          const SizedBox(height: 24),
        ],
      ),
    );
  }

  Widget _buildDashboardTab() {
    final calibTimeProgress = (_guidedCalibrationElapsed.inMilliseconds / _minCalibrationDuration.inMilliseconds)
        .clamp(0.0, 1.0);

    return ListView(
      padding: const EdgeInsets.all(16),
      children: [
        Card(
          child: Container(
            padding: const EdgeInsets.all(14),
            decoration: BoxDecoration(
              borderRadius: BorderRadius.circular(12),
              gradient: LinearGradient(
                colors: [
                  Theme.of(context).colorScheme.secondary.withValues(alpha: 0.18),
                  Theme.of(context).colorScheme.primary.withValues(alpha: 0.10),
                ],
                begin: Alignment.topLeft,
                end: Alignment.bottomRight,
              ),
            ),
            child: Wrap(
              spacing: 8,
              runSpacing: 8,
              children: [
                _MiniPill(text: _connected ? "Live connected" : "Offline"),
                _MiniPill(text: "ML ${_mlModelLoaded ? "ON" : "OFF"}"),
                _MiniPill(text: "Parse $_parseStatus"),
                _MiniPill(text: _stressResult?.levelText ?? "Stress N/A"),
                _MiniPill(text: _stressEngine.calibrationReady ? "Calibrated" : "Uncalibrated"),
              ],
            ),
          ),
        ),
        const SizedBox(height: 12),
        Card(
          child: Padding(
            padding: const EdgeInsets.all(14),
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                const Text("Measure stress", style: TextStyle(fontSize: 16, fontWeight: FontWeight.w600)),
                const SizedBox(height: 6),
                Text(
                  _stressMeasureActive
                      ? "Measuring now. Keep good sensor contact and stay still."
                      : "Press Measure stress to run a timed measurement and get a final output.",
                ),
                const SizedBox(height: 10),
                if (_stressMeasureActive) ...[
                  Row(
                    mainAxisAlignment: MainAxisAlignment.spaceBetween,
                    children: [
                      Text("Time left ${_fmtDuration(_stressMeasureRemaining)}"),
                      Text(_fmtDuration(_stressMeasureElapsed)),
                    ],
                  ),
                  const SizedBox(height: 6),
                  LinearProgressIndicator(value: _stressMeasureProgress),
                  const SizedBox(height: 10),
                  Wrap(
                    spacing: 8,
                    runSpacing: 8,
                    children: [
                      _MiniPill(text: "Valid $_measureValidSamples"),
                      _MiniPill(text: "Invalid $_measureInvalidSamples"),
                      _MiniPill(text: "Min valid $_measureMinValidSamples"),
                    ],
                  ),
                ],
                if (_measureLiveIssue != null) ...[
                  const SizedBox(height: 8),
                  Text(
                    _measureLiveIssue!,
                    style: TextStyle(color: Theme.of(context).colorScheme.error),
                  ),
                ],
                if (_lastMeasureSummary != null && !_stressMeasureActive) ...[
                  const SizedBox(height: 8),
                  Wrap(
                    spacing: 8,
                    runSpacing: 8,
                    children: [
                      _MiniPill(text: "Last ${_lastMeasureSummary!.level}"),
                      _MiniPill(text: "Score ${_lastMeasureSummary!.score.toStringAsFixed(3)}"),
                      _MiniPill(text: "Conf ${(100 * _lastMeasureSummary!.confidence).toStringAsFixed(0)}%"),
                    ],
                  ),
                ],
                const SizedBox(height: 10),
                Wrap(
                  spacing: 10,
                  runSpacing: 10,
                  children: [
                    FilledButton.icon(
                      onPressed: (_stressMeasureActive || !_connected) ? null : _startStressMeasurement,
                      icon: const Icon(Icons.play_arrow),
                      label: const Text("Measure stress"),
                    ),
                    OutlinedButton.icon(
                      onPressed: _stressMeasureActive ? _cancelStressMeasurement : null,
                      icon: const Icon(Icons.stop),
                      label: const Text("Cancel"),
                    ),
                  ],
                ),
              ],
            ),
          ),
        ),
        const SizedBox(height: 12),
        if (_guidedCalibrationActive)
          Card(
            child: Padding(
              padding: const EdgeInsets.all(14),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  const Text("Calibration in progress", style: TextStyle(fontSize: 16, fontWeight: FontWeight.w600)),
                  const SizedBox(height: 8),
                  Text("User $_activeUserId"),
                  const SizedBox(height: 6),
                  Row(
                    children: [
                      Icon(
                        _calibrationHasValidSignals ? Icons.check_circle : Icons.sensors_off,
                        size: 16,
                        color: _calibrationHasValidSignals ? Colors.greenAccent : Colors.orangeAccent,
                      ),
                      const SizedBox(width: 8),
                      Expanded(
                        child: Text(
                          _calibrationHasValidSignals
                              ? "Valid signals detected. Collecting windows."
                              : "Waiting for valid HR, GSR, and Temp values above 0.",
                        ),
                      ),
                    ],
                  ),
                  const SizedBox(height: 10),
                  Row(
                    mainAxisAlignment: MainAxisAlignment.spaceBetween,
                    children: [
                      Text("Time left ${_fmtDuration(_guidedCalibrationRemaining)}"),
                      Text("${_fmtDuration(_guidedCalibrationElapsed)} / ${_fmtDuration(_minCalibrationDuration)}"),
                    ],
                  ),
                  const SizedBox(height: 6),
                  LinearProgressIndicator(value: calibTimeProgress),
                  const SizedBox(height: 10),
                  Row(
                    mainAxisAlignment: MainAxisAlignment.spaceBetween,
                    children: [
                      const Text("Valid samples collected"),
                      Text(
                        "${_stressEngine.baselineCollected} (min ${_stressEngine.baselineTarget})",
                      ),
                    ],
                  ),
                  const SizedBox(height: 6),
                  Text("Invalid ignored $_calibrationInvalidSamples"),
                ],
              ),
            ),
          ),
        if (_guidedCalibrationActive) const SizedBox(height: 12),
        _MetricsGrid(
          ts: _ts,
          bpm: _bpm,
          gsr: _gsr,
          temp: _temp,
          stressResult: _stressResult,
          stressInputIssue: _stressInputIssue,
          measuredSummary: _lastMeasureSummary,
          stressMeasureActive: _stressMeasureActive,
          mlModelLoaded: _mlModelLoaded,
          calibrationWindows: _stressEngine.baselineCollected,
          calibrationTarget: _stressEngine.baselineTarget,
          windowSamples: _stressEngine.currentWindowSamples,
          windowTarget: _stressEngine.windowTarget,
          calibrationReady: _stressEngine.calibrationReady,
          bpmHistory: _bpmHistory,
          gsrHistory: _gsrHistory,
          tempHistory: _tempHistory,
          stressHistory: _stressHistory,
          guidedCalibrationActive: _guidedCalibrationActive,
          calibrationElapsedText: _fmtDuration(_guidedCalibrationElapsed),
          calibrationRemainingText: _fmtDuration(_guidedCalibrationRemaining),
          calibrationTimeDone: _guidedCalibrationTimeDone,
          calibrationElapsedMinuteText: _fmtMinuteProgress(_guidedCalibrationElapsed, _minCalibrationDuration),
          onOpenStressDetails: _openStressDetailsPage,
          onOpenBpmGraph: () => _openGraphPage(title: "BPM Trend", unit: "bpm", data: _bpmHistory),
          onOpenGsrGraph: () => _openGraphPage(title: "GSR Trend", unit: "uS", data: _gsrHistory),
          onOpenStressGraph: () => _openGraphPage(title: "Stress Score Trend", unit: "score", data: _stressHistory),
        ),
        const SizedBox(height: 24),
      ],
    );
  }

  Widget _buildAboutTab() {
    String s(dynamic v) => v == null ? "N/A" : v.toString();
    final random = (_modelMetrics["random_split_metrics"] is Map<String, dynamic>)
        ? (_modelMetrics["random_split_metrics"] as Map<String, dynamic>)
        : const <String, dynamic>{};
    final blocked = (_modelMetrics["blocked_split_metrics"] is Map<String, dynamic>)
        ? (_modelMetrics["blocked_split_metrics"] as Map<String, dynamic>)
        : const <String, dynamic>{};
    final legacyAccuracy = _modelMetrics["accuracy"];
    final legacyF1 = _modelMetrics["f1"];
    final randomAccuracy = random["accuracy"] ?? legacyAccuracy;
    final randomF1 = random["f1_macro"] ?? legacyF1;
    final blockedAccuracy = blocked["accuracy"];
    final blockedF1 = blocked["f1_macro"];
    return ListView(
      padding: const EdgeInsets.all(16),
      children: [
        _CardSection(
          title: "Open source",
          subtitle: "Transparency and model provenance",
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Text(s(_modelInfo["open_source_note"])),
              const SizedBox(height: 10),
              _MiniPill(text: "App ${s(_modelInfo["app_version"])}"),
              const SizedBox(height: 8),
              _MiniPill(text: "Model ${s(_modelInfo["model_version"])}"),
              const SizedBox(height: 8),
              _MiniPill(text: "ML ${_mlModelLoaded ? "ON" : "OFF"}"),
            ],
          ),
        ),
        const SizedBox(height: 12),
        _CardSection(
          title: "Dataset",
          subtitle: "Training dataset metadata",
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Text("Name: ${s(_modelInfo["dataset_name"])}"),
              Text("Source: ${s(_modelInfo["dataset_source"])}"),
              Text("DOI: ${s(_modelInfo["dataset_doi"])}"),
              Text("PMID: ${s(_modelInfo["dataset_pmid"])}"),
              Text("PMCID: ${s(_modelInfo["dataset_pmcid"])}"),
              Text("Repository: ${s(_modelInfo["dataset_repository"])}"),
              Text("Repository DOI: ${s(_modelInfo["dataset_repository_doi"])}"),
              Text("Version: ${s(_modelInfo["dataset_version"])}"),
              Text("Dataset date: ${s(_modelInfo["dataset_date"])}"),
              Text("Last update: ${s(_modelInfo["dataset_last_update"])}"),
              Text("Subjects: ${s(_modelInfo["dataset_subjects"])}"),
              Text("Instances: ${s(_modelInfo["dataset_instances"])}"),
              Text("Collection period: ${s(_modelInfo["dataset_collection_period"])}"),
              Text("Total hours: ${s(_modelInfo["dataset_total_hours"])}"),
              Text("Modalities: ${s(_modelInfo["dataset_modalities"])}"),
            ],
          ),
        ),
        const SizedBox(height: 12),
        _CardSection(
          title: "Calibration",
          subtitle: "Personal baseline for your own physiology",
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              const Text(
                "How to calibrate: sit calmly for 2 to 5 minutes, normal breathing, minimal movement, good sensor contact.",
              ),
              const SizedBox(height: 6),
              const Text("Calibration windows are collected only when HR, GSR, and Temp are valid values above 0."),
              const SizedBox(height: 8),
              Wrap(
                spacing: 8,
                runSpacing: 8,
                children: [
                  _MiniPill(text: "Status ${_stressEngine.calibrationReady ? "Ready" : "Not ready"}"),
                  _MiniPill(text: "Valid samples ${_stressEngine.baselineCollected} (min ${_stressEngine.baselineTarget})"),
                  _MiniPill(text: "Invalid ignored $_calibrationInvalidSamples"),
                  _MiniPill(text: "Time ${_fmtMinuteProgress(_guidedCalibrationElapsed, _minCalibrationDuration)}"),
                  _MiniPill(text: "Time left ${_fmtDuration(_guidedCalibrationRemaining)}"),
                  _MiniPill(text: "Mode ${_guidedCalibrationActive ? "Calibrating" : "Idle"}"),
                  _MiniPill(text: "User $_activeUserId"),
                  _MiniPill(text: _connected ? "Device connected" : "Connect device to calibrate"),
                ],
              ),
              const SizedBox(height: 10),
              Wrap(
                spacing: 10,
                runSpacing: 10,
                children: [
                  FilledButton.icon(
                    onPressed: (_guidedCalibrationActive || !_connected) ? null : _startGuidedCalibrationWithUserPrompt,
                    icon: const Icon(Icons.play_arrow),
                    label: const Text("Calibrate now"),
                  ),
                  OutlinedButton.icon(
                    onPressed: _guidedCalibrationActive ? _stopGuidedCalibration : null,
                    icon: const Icon(Icons.stop),
                    label: const Text("Stop"),
                  ),
                  OutlinedButton.icon(
                    onPressed: _resetCalibration,
                    icon: const Icon(Icons.tune),
                    label: const Text("Reset baseline"),
                  ),
                ],
              ),
            ],
          ),
        ),
        const SizedBox(height: 12),
        _CardSection(
          title: "Model performance",
          subtitle: "Exported training metrics",
          child: Wrap(
            spacing: 8,
            runSpacing: 8,
            children: [
              _MiniPill(text: "Random acc ${randomAccuracy == null ? "N/A" : (randomAccuracy as num).toStringAsFixed(3)}"),
              _MiniPill(text: "Random F1 ${randomF1 == null ? "N/A" : (randomF1 as num).toStringAsFixed(3)}"),
              _MiniPill(text: "Blocked acc ${blockedAccuracy == null ? "N/A" : (blockedAccuracy as num).toStringAsFixed(3)}"),
              _MiniPill(text: "Blocked F1 ${blockedF1 == null ? "N/A" : (blockedF1 as num).toStringAsFixed(3)}"),
              _MiniPill(text: "Rows ${s(_modelMetrics["rows_total"])}"),
              _MiniPill(text: "CV best F1w ${_modelMetrics["cv_best_score_f1_weighted"] == null ? "N/A" : ((_modelMetrics["cv_best_score_f1_weighted"] as num).toStringAsFixed(3))}"),
              _MiniPill(text: "Selected ${s(_modelMetrics["selected_model"])}"),
            ],
          ),
        ),
        const SizedBox(height: 12),
        _CardSection(
          title: "Developer",
          subtitle: "Data collection and labeling for fine tuning",
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              OutlinedButton.icon(
                onPressed: () => setState(() => _showDeveloperTools = !_showDeveloperTools),
                icon: const Icon(Icons.developer_mode),
                label: Text(_showDeveloperTools ? "Hide developer tools" : "I am a developer"),
              ),
              if (_showDeveloperTools) ...[
                const SizedBox(height: 10),
                TextField(
                  controller: _userIdController,
                  decoration: const InputDecoration(
                    labelText: "Developer user ID",
                    border: OutlineInputBorder(),
                  ),
                ),
                const SizedBox(height: 8),
                Wrap(
                  spacing: 10,
                  runSpacing: 10,
                  children: [
                    FilledButton.icon(
                      onPressed: () => _switchCalibrationUser(_userIdController.text),
                      icon: const Icon(Icons.person),
                      label: const Text("Load user profile"),
                    ),
                  ],
                ),
                const SizedBox(height: 10),
                Text("Session label", style: TextStyle(color: Colors.white.withValues(alpha: 0.8))),
                const SizedBox(height: 8),
                SegmentedButton<SessionLabel>(
                  segments: const [
                    ButtonSegment(value: SessionLabel.unlabeled, label: Text("Unlabeled")),
                    ButtonSegment(value: SessionLabel.rest, label: Text("Rest")),
                    ButtonSegment(value: SessionLabel.stressTask, label: Text("Stress")),
                    ButtonSegment(value: SessionLabel.recovery, label: Text("Recovery")),
                  ],
                  selected: {_sessionLabel},
                  onSelectionChanged: (set) {
                    if (set.isEmpty) return;
                    setState(() => _sessionLabel = set.first);
                  },
                ),
                const SizedBox(height: 10),
                Wrap(
                  spacing: 8,
                  runSpacing: 8,
                  children: [
                    _MiniPill(text: "Label ${_sessionLabel.title}"),
                    _MiniPill(text: "CSV rows $_loggedRows"),
                    _MiniPill(text: "Path ${_historyCsvPath ?? "N/A"}"),
                    _MiniPill(text: "Raw bytes ${_raw.length}"),
                  ],
                ),
                const SizedBox(height: 10),
                Wrap(
                  spacing: 10,
                  runSpacing: 10,
                  children: [
                    FilledButton.icon(
                      onPressed: _openHistoryPage,
                      icon: const Icon(Icons.table_chart),
                      label: const Text("View history"),
                    ),
                    OutlinedButton.icon(
                      onPressed: _copyHistoryCsvToClipboard,
                      icon: const Icon(Icons.copy),
                      label: const Text("Copy CSV"),
                    ),
                    OutlinedButton.icon(
                      onPressed: () async {
                        await Clipboard.setData(ClipboardData(text: _raw));
                        if (!mounted) return;
                        await _showToast("Copied raw to clipboard");
                      },
                      icon: const Icon(Icons.code),
                      label: const Text("Copy raw"),
                    ),
                  ],
                ),
                const SizedBox(height: 10),
                _CardSection(
                  title: "Raw BLE stream",
                  subtitle: "Developer debug view",
                  child: Container(
                    padding: const EdgeInsets.all(12),
                    decoration: BoxDecoration(
                      color: Colors.black.withValues(alpha: 0.25),
                      borderRadius: BorderRadius.circular(12),
                      border: Border.all(color: Colors.white.withValues(alpha: 0.08)),
                    ),
                    child: SelectableText(
                      _raw.isEmpty ? "(empty)" : _raw,
                      style: const TextStyle(fontFamily: "monospace", fontSize: 12),
                    ),
                  ),
                ),
              ],
            ],
          ),
        ),
        const SizedBox(height: 24),
      ],
    );
  }

  @override
  Widget build(BuildContext context) {
    final connectedName = _device?.platformName.isNotEmpty == true
        ? _device!.platformName
        : _device?.remoteId.str;
    final tabTitles = ["Connection", "Dashboard", "About"];

    return Scaffold(
      appBar: AppBar(
        title: Text(tabTitles[_tabIndex]),
        actions: [
          _StatusPill(text: _status),
          const SizedBox(width: 10),
        ],
      ),
      floatingActionButton: _connected
          ? FloatingActionButton.extended(
              onPressed: _reconnecting ? null : _reconnect,
              icon: const Icon(Icons.refresh),
              label: Text(_reconnecting ? "Refreshing" : "Refresh"),
            )
          : null,
      body: IndexedStack(
        index: _tabIndex,
        children: [
          _buildConnectionTab(connectedName),
          _buildDashboardTab(),
          _buildAboutTab(),
        ],
      ),
      bottomNavigationBar: NavigationBar(
        selectedIndex: _tabIndex,
        onDestinationSelected: (index) => setState(() => _tabIndex = index),
        destinations: const [
          NavigationDestination(icon: Icon(Icons.bluetooth_searching), label: "Connection"),
          NavigationDestination(icon: Icon(Icons.monitor_heart), label: "Dashboard"),
          NavigationDestination(icon: Icon(Icons.info_outline), label: "About"),
        ],
      ),
    );
  }
}

class MetricGroup {
  final double? avg;
  final double? min;
  final double? max;
  final double? std;

  const MetricGroup({this.avg, this.min, this.max, this.std});

  static double? _toDouble(dynamic v) {
    if (v is num) return v.toDouble();
    if (v is String) return double.tryParse(v);
    return null;
  }

  factory MetricGroup.fromMap(Map<String, dynamic> m) {
    return MetricGroup(
      avg: _toDouble(m["avg"] ?? m["a"]),
      min: _toDouble(m["min"] ?? m["m"]),
      max: _toDouble(m["max"] ?? m["x"]),
      std: _toDouble(m["std"] ?? m["s"]),
    );
  }
}

class JsonChunkAssembler {
  final StringBuffer _buf = StringBuffer();
  static const int _maxRemainder = 5000;
  static const int _maxBuffer = 12000;
  static final RegExp _packetStart = RegExp(r'\{"(?:ts|TS)"\s*:');

  void reset() => _buf.clear();
  int get pendingBytes => _buf.length;

  List<Map<String, dynamic>> push(String chunk) {
    if (chunk.isEmpty) return const [];
    _buf.write(chunk);

    if (_buf.length > _maxBuffer) {
      final s = _buf.toString();
      final keep = s.substring(s.length - _maxBuffer);
      _buf
        ..clear()
        ..write(keep);
    }

    final text = _buf.toString();
    final objects = <Map<String, dynamic>>[];
    final starts = _packetStart.allMatches(text).map((m) => m.start).toList(growable: false);

    if (starts.length >= 2) {
      for (int i = 0; i < starts.length - 1; i++) {
        final segment = text.substring(starts[i], starts[i + 1]);
        final parsed = _parseSegment(segment);
        if (parsed != null) {
          objects.add(parsed);
        }
      }

      final rem = text.substring(starts.last);
      final safe = rem.length > _maxRemainder ? rem.substring(rem.length - _maxRemainder) : rem;
      _buf
        ..clear()
        ..write(safe);
      return objects;
    }

    if (starts.length == 1) {
      final segment = text.substring(starts.first);
      final parsed = _parseSegment(segment);
      if (parsed != null) {
        objects.add(parsed);
        final lastBrace = segment.lastIndexOf("}");
        final consumed = starts.first + lastBrace + 1;
        final rem = text.substring(consumed);
        final safe = rem.length > _maxRemainder ? rem.substring(rem.length - _maxRemainder) : rem;
        _buf
          ..clear()
          ..write(safe);
        return objects;
      }
    }

    if (_buf.length > _maxRemainder) {
      final idx = text.lastIndexOf("{");
      _buf.clear();
      if (idx >= 0) {
        _buf.write(text.substring(idx));
      } else {
        _buf.write(text.substring(text.length - _maxRemainder));
      }
    }

    return objects;
  }

  Map<String, dynamic>? _parseSegment(String segment) {
    int end = segment.lastIndexOf("}");
    while (end >= 0) {
      final candidate = segment.substring(0, end + 1);
      final parsed = _tryParse(candidate);
      if (parsed != null && _looksLikePayload(parsed)) {
        return parsed;
      }
      end = segment.lastIndexOf("}", end - 1);
    }
    return null;
  }

  bool _looksLikePayload(Map<String, dynamic> m) {
    return m.containsKey("ts") ||
        m.containsKey("TS") ||
        m.containsKey("BPM") ||
        m.containsKey("bpm") ||
        m.containsKey("GSR") ||
        m.containsKey("gsr");
  }

  Map<String, dynamic>? _tryParse(String s) {
    try {
      final v = json.decode(s);
      if (v is Map<String, dynamic>) return v;
      if (v is Map) return v.cast<String, dynamic>();
      return null;
    } catch (_) {
      return null;
    }
  }
}

class _TopActions extends StatelessWidget {
  final bool scanning;
  final bool connecting;
  final bool connected;
  final bool canReconnectLast;
  final String? connectedName;
  final String parseStatus;
  final bool mlModelLoaded;
  final TextEditingController filterController;
  final ValueChanged<String> onFilterChanged;
  final VoidCallback onAutoFilterEsp32;
  final VoidCallback onScan;
  final VoidCallback onStopScan;
  final VoidCallback onDisconnect;
  final VoidCallback onReconnect;
  final VoidCallback onResetSession;

  const _TopActions({
    required this.scanning,
    required this.connecting,
    required this.connected,
    required this.canReconnectLast,
    required this.connectedName,
    required this.parseStatus,
    required this.mlModelLoaded,
    required this.filterController,
    required this.onFilterChanged,
    required this.onAutoFilterEsp32,
    required this.onScan,
    required this.onStopScan,
    required this.onDisconnect,
    required this.onReconnect,
    required this.onResetSession,
  });

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;

    return Card(
      child: Padding(
        padding: const EdgeInsets.all(14),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Wrap(
              runSpacing: 10,
              spacing: 10,
              children: [
                FilledButton.icon(
                  onPressed: scanning ? null : onScan,
                  icon: const Icon(Icons.radar),
                  label: Text(scanning ? "Scanning" : "Scan"),
                ),
                OutlinedButton.icon(
                  onPressed: scanning ? onStopScan : null,
                  icon: const Icon(Icons.stop),
                  label: const Text("Stop"),
                ),
                if (connected)
                  FilledButton.tonalIcon(
                    onPressed: onDisconnect,
                    icon: const Icon(Icons.link_off),
                    label: const Text("Disconnect"),
                  ),
                if (connected)
                  FilledButton.tonalIcon(
                    onPressed: onReconnect,
                    icon: const Icon(Icons.refresh),
                    label: const Text("Reconnect"),
                  ),
                if (canReconnectLast)
                  FilledButton.tonalIcon(
                    onPressed: onReconnect,
                    icon: const Icon(Icons.history_toggle_off),
                    label: const Text("Reconnect last"),
                  ),
                if (connected)
                  OutlinedButton.icon(
                    onPressed: onResetSession,
                    icon: const Icon(Icons.restart_alt),
                    label: const Text("Reset sensor session"),
                  ),
              ],
            ),
            const SizedBox(height: 12),
            TextField(
              controller: filterController,
              decoration: const InputDecoration(
                labelText: "Device name filter",
                hintText: "ESP32_HealthMonitor",
                border: OutlineInputBorder(),
              ),
              onChanged: onFilterChanged,
            ),
            const SizedBox(height: 8),
            Wrap(
              spacing: 8,
              runSpacing: 8,
              children: [
                OutlinedButton.icon(
                  onPressed: onAutoFilterEsp32,
                  icon: const Icon(Icons.filter_alt),
                  label: const Text("Auto filter ESP32"),
                ),
              ],
            ),
            const SizedBox(height: 12),
            Container(
              padding: const EdgeInsets.all(12),
              decoration: BoxDecoration(
                borderRadius: BorderRadius.circular(12),
                color: cs.surfaceContainerHighest.withValues(alpha: 0.35),
                border: Border.all(color: Colors.white.withValues(alpha: 0.08)),
              ),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  Row(
                    children: [
                      Icon(connected ? Icons.bluetooth_connected : Icons.bluetooth, size: 18),
                      const SizedBox(width: 10),
                      Expanded(
                        child: Text(
                          connected ? "Connected to ${connectedName ?? "device"}" : (connecting ? "Connecting..." : "Not connected"),
                          maxLines: 1,
                          overflow: TextOverflow.ellipsis,
                        ),
                      ),
                    ],
                  ),
                  const SizedBox(height: 8),
                  Wrap(
                    spacing: 8,
                    runSpacing: 8,
                    children: [
                      _MiniPill(text: "Parse: $parseStatus"),
                      _MiniPill(text: "ML ${mlModelLoaded ? "ON" : "OFF"}"),
                    ],
                  ),
                ],
              ),
            ),
          ],
        ),
      ),
    );
  }
}

class _MetricsGrid extends StatelessWidget {
  final int? ts;
  final MetricGroup? bpm;
  final MetricGroup? gsr;
  final double? temp;
  final StressInferenceResult? stressResult;
  final String? stressInputIssue;
  final _MeasureSummary? measuredSummary;
  final bool stressMeasureActive;
  final bool mlModelLoaded;
  final int calibrationWindows;
  final int calibrationTarget;
  final int windowSamples;
  final int windowTarget;
  final bool calibrationReady;
  final List<double> bpmHistory;
  final List<double> gsrHistory;
  final List<double> tempHistory;
  final List<double> stressHistory;
  final bool guidedCalibrationActive;
  final String calibrationElapsedText;
  final String calibrationRemainingText;
  final bool calibrationTimeDone;
  final String calibrationElapsedMinuteText;
  final VoidCallback onOpenStressDetails;
  final VoidCallback onOpenBpmGraph;
  final VoidCallback onOpenGsrGraph;
  final VoidCallback onOpenStressGraph;

  const _MetricsGrid({
    required this.ts,
    required this.bpm,
    required this.gsr,
    required this.temp,
    required this.stressResult,
    required this.stressInputIssue,
    required this.measuredSummary,
    required this.stressMeasureActive,
    required this.mlModelLoaded,
    required this.calibrationWindows,
    required this.calibrationTarget,
    required this.windowSamples,
    required this.windowTarget,
    required this.calibrationReady,
    required this.bpmHistory,
    required this.gsrHistory,
    required this.tempHistory,
    required this.stressHistory,
    required this.guidedCalibrationActive,
    required this.calibrationElapsedText,
    required this.calibrationRemainingText,
    required this.calibrationTimeDone,
    required this.calibrationElapsedMinuteText,
    required this.onOpenStressDetails,
    required this.onOpenBpmGraph,
    required this.onOpenGsrGraph,
    required this.onOpenStressGraph,
  });

  @override
  Widget build(BuildContext context) {
    final stressText = stressMeasureActive ? "Measuring..." : (measuredSummary?.level ?? "Not measured");
    final confidenceCombined = measuredSummary == null
        ? "N/A"
        : "${(measuredSummary!.confidence * 100).toStringAsFixed(0)}% "
            "(${measuredSummary!.confidence >= 0.75 ? "High" : (measuredSummary!.confidence >= 0.45 ? "Medium" : "Low")})";
    final bpmAvgDisplay = _fmt(bpm?.avg);
    final gsrAvgDisplay = _fmt(gsr?.avg);
    final tempAvgDisplay = _fmt(temp);

    return Card(
      child: Padding(
        padding: const EdgeInsets.all(14),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            const Text("Live averages", style: TextStyle(fontSize: 16, fontWeight: FontWeight.w600)),
            const SizedBox(height: 4),
            const Text("Simple view for BPM, GSR, and temperature"),
            const SizedBox(height: 10),
            Wrap(
              spacing: 10,
              runSpacing: 10,
              children: [
                _ExpandableMetricCard(
                  title: "BPM",
                  icon: Icons.favorite,
                  accent: const Color(0xFFE11D48),
                  primaryValue: bpmAvgDisplay,
                  primaryUnit: "Average BPM",
                  details: const [],
                ),
                _ExpandableMetricCard(
                  title: "GSR",
                  icon: Icons.waves,
                  accent: const Color(0xFF14B8A6),
                  primaryValue: gsrAvgDisplay,
                  primaryUnit: "Average GSR",
                  details: const [],
                ),
                _ExpandableMetricCard(
                  title: "Temperature",
                  icon: Icons.thermostat,
                  accent: const Color(0xFFF59E0B),
                  primaryValue: tempAvgDisplay,
                  primaryUnit: "Average °C",
                  details: const [],
                ),
                _ExpandableMetricCard(
                  title: "Stress",
                  icon: Icons.psychology_alt,
                  accent: const Color(0xFF6366F1),
                  primaryValue: stressText,
                  primaryUnit: "level",
                  details: [
                    ("Confidence", confidenceCombined),
                  ],
                  footer: Align(
                    alignment: Alignment.centerRight,
                    child: OutlinedButton.icon(
                      onPressed: onOpenStressDetails,
                      icon: const Icon(Icons.open_in_new),
                      label: const Text("Open details"),
                    ),
                  ),
                ),
              ],
            ),
            const SizedBox(height: 14),
            _MiniSparkline(title: "BPM trend", data: bpmHistory, onTap: onOpenBpmGraph),
            const SizedBox(height: 10),
            _MiniSparkline(title: "GSR trend", data: gsrHistory, onTap: onOpenGsrGraph),
            const SizedBox(height: 10),
            _MiniSparkline(title: "Stress score trend", data: stressHistory, onTap: onOpenStressGraph),
          ],
        ),
      ),
    );
  }

  String _fmt(double? v) => v == null ? "N/A" : v.toStringAsFixed(1);
}

class _ExpandableMetricCard extends StatelessWidget {
  final String title;
  final IconData icon;
  final Color accent;
  final String primaryValue;
  final String primaryUnit;
  final List<(String, String)> details;
  final Widget? footer;

  const _ExpandableMetricCard({
    required this.title,
    required this.icon,
    required this.accent,
    required this.primaryValue,
    required this.primaryUnit,
    required this.details,
    this.footer,
  });

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;
    return ConstrainedBox(
      constraints: const BoxConstraints(minWidth: 280, maxWidth: 520),
      child: Container(
        decoration: BoxDecoration(
          borderRadius: BorderRadius.circular(16),
          gradient: LinearGradient(
            colors: [
              accent.withValues(alpha: 0.18),
              cs.surfaceContainerHighest.withValues(alpha: 0.26),
            ],
            begin: Alignment.topLeft,
            end: Alignment.bottomRight,
          ),
          border: Border.all(color: Colors.white.withValues(alpha: 0.09)),
        ),
        child: Theme(
          data: Theme.of(context).copyWith(dividerColor: Colors.transparent),
          child: ExpansionTile(
            tilePadding: const EdgeInsets.symmetric(horizontal: 14, vertical: 6),
            childrenPadding: const EdgeInsets.fromLTRB(14, 0, 14, 12),
            leading: Container(
              width: 34,
              height: 34,
              decoration: BoxDecoration(
                color: accent.withValues(alpha: 0.24),
                borderRadius: BorderRadius.circular(10),
              ),
              child: Icon(icon, size: 18),
            ),
            title: Text(title, style: const TextStyle(fontWeight: FontWeight.w700)),
            subtitle: Text(primaryUnit),
            trailing: Text(
              primaryValue,
              style: const TextStyle(fontWeight: FontWeight.w800, fontSize: 18),
            ),
            children: [
              ...details.map((d) => _DetailRow(label: d.$1, value: d.$2)),
              if (footer != null) ...[
                const SizedBox(height: 6),
                footer!,
              ],
            ],
          ),
        ),
      ),
    );
  }
}

class _DetailRow extends StatelessWidget {
  final String label;
  final String value;

  const _DetailRow({required this.label, required this.value});

  @override
  Widget build(BuildContext context) {
    return Padding(
      padding: const EdgeInsets.symmetric(vertical: 4),
      child: Row(
        children: [
          Expanded(
            child: Text(
              label,
              style: TextStyle(color: Colors.white.withValues(alpha: 0.72)),
            ),
          ),
          Text(
            value,
            style: const TextStyle(fontWeight: FontWeight.w700),
          ),
        ],
      ),
    );
  }
}

class _MiniSparkline extends StatelessWidget {
  final String title;
  final List<double> data;
  final VoidCallback onTap;

  const _MiniSparkline({required this.title, required this.data, required this.onTap});

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;

    return InkWell(
      borderRadius: BorderRadius.circular(14),
      onTap: onTap,
      child: Container(
        padding: const EdgeInsets.all(12),
        decoration: BoxDecoration(
          borderRadius: BorderRadius.circular(14),
          color: cs.surfaceContainerHighest.withValues(alpha: 0.22),
          border: Border.all(color: Colors.white.withValues(alpha: 0.08)),
        ),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Row(
              children: [
                Expanded(
                  child: Text(title, style: const TextStyle(fontWeight: FontWeight.w600)),
                ),
                const Icon(Icons.open_in_full, size: 16),
              ],
            ),
            const SizedBox(height: 8),
            SizedBox(
              height: 42,
              child: CustomPaint(
                painter: _SparkPainter(data),
                child: const SizedBox.expand(),
              ),
            ),
          ],
        ),
      ),
    );
  }
}

class _SparkPainter extends CustomPainter {
  final List<double> data;
  _SparkPainter(this.data);

  @override
  void paint(Canvas canvas, Size size) {
    if (data.length < 2) return;

    final minV = data.reduce(min);
    final maxV = data.reduce(max);
    final span = (maxV - minV).abs() < 1e-9 ? 1.0 : (maxV - minV);

    final paintLine = Paint()
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    final path = Path();

    for (int i = 0; i < data.length; i++) {
      final x = size.width * (i / (data.length - 1));
      final norm = (data[i] - minV) / span;
      final y = size.height * (1.0 - norm);

      if (i == 0) {
        path.moveTo(x, y);
      } else {
        path.lineTo(x, y);
      }
    }

    canvas.drawPath(path, paintLine);
  }

  @override
  bool shouldRepaint(covariant _SparkPainter oldDelegate) => oldDelegate.data != data;
}

class _GraphDetailPage extends StatelessWidget {
  final String title;
  final String unit;
  final List<double> data;

  const _GraphDetailPage({
    required this.title,
    required this.unit,
    required this.data,
  });

  @override
  Widget build(BuildContext context) {
    final minV = data.isEmpty ? null : data.reduce(min);
    final maxV = data.isEmpty ? null : data.reduce(max);
    final avgV = data.isEmpty ? null : data.reduce((a, b) => a + b) / data.length;
    final width = max(480.0, data.length * 26.0);
    return Scaffold(
      appBar: AppBar(title: Text(title)),
      body: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          _CardSection(
            title: "Interactive graph",
            subtitle: "Pinch to zoom and pan horizontally",
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Wrap(
                  spacing: 8,
                  runSpacing: 8,
                  children: [
                    _MiniPill(text: "Points ${data.length}"),
                    _MiniPill(text: "Min ${minV?.toStringAsFixed(2) ?? "N/A"} $unit"),
                    _MiniPill(text: "Max ${maxV?.toStringAsFixed(2) ?? "N/A"} $unit"),
                    _MiniPill(text: "Avg ${avgV?.toStringAsFixed(2) ?? "N/A"} $unit"),
                  ],
                ),
                const SizedBox(height: 12),
                Container(
                  height: 280,
                  decoration: BoxDecoration(
                    borderRadius: BorderRadius.circular(12),
                    border: Border.all(color: Colors.white.withValues(alpha: 0.10)),
                    color: Theme.of(context).colorScheme.surfaceContainerHighest.withValues(alpha: 0.24),
                  ),
                  child: data.length < 2
                      ? const Center(child: Text("Not enough data yet"))
                      : InteractiveViewer(
                          minScale: 1.0,
                          maxScale: 8.0,
                          constrained: false,
                          child: SizedBox(
                            width: width,
                            height: 260,
                            child: CustomPaint(
                              painter: _SparkPainter(data),
                            ),
                          ),
                        ),
                ),
              ],
            ),
          ),
        ],
      ),
    );
  }
}

class _StressDetailsPage extends StatelessWidget {
  final _MeasureSummary? measuredSummary;
  final StressInferenceResult? stressResult;
  final String? stressInputIssue;
  final bool mlModelLoaded;
  final bool calibrationReady;
  final int calibrationSamples;
  final int calibrationSampleMin;
  final String calibrationElapsedText;
  final String calibrationRemainingText;
  final String inferenceWindowText;
  final bool guidedCalibrationActive;

  const _StressDetailsPage({
    required this.measuredSummary,
    required this.stressResult,
    required this.stressInputIssue,
    required this.mlModelLoaded,
    required this.calibrationReady,
    required this.calibrationSamples,
    required this.calibrationSampleMin,
    required this.calibrationElapsedText,
    required this.calibrationRemainingText,
    required this.inferenceWindowText,
    required this.guidedCalibrationActive,
  });

  @override
  Widget build(BuildContext context) {
    final activeScore = measuredSummary?.score ?? stressResult?.stressProbability;
    final activeConfidence = measuredSummary?.confidence ?? stressResult?.confidence;
    final activeLevel = measuredSummary?.level ?? stressResult?.levelText;
    final confidence = activeConfidence == null ? "N/A" : "${(activeConfidence * 100).toStringAsFixed(0)}%";
    final confidenceLevel = activeConfidence == null
        ? "N/A"
        : (activeConfidence >= 0.75
            ? "High"
            : (activeConfidence >= 0.45 ? "Medium" : "Low"));
    final stressScore = activeScore == null ? "N/A" : activeScore.toStringAsFixed(3);
    final cortisolProxy = activeScore == null ? "N/A" : (activeScore * 100).toStringAsFixed(1);
    final stressLevel = activeLevel ?? "N/A";

    return Scaffold(
      appBar: AppBar(title: const Text("Stress Details")),
      body: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          _CardSection(
            title: "Current output",
            subtitle: "Live inference fields",
            child: Wrap(
              spacing: 8,
              runSpacing: 8,
              children: [
                _MiniPill(text: "Stress level $stressLevel"),
                _MiniPill(text: "Stress score $stressScore"),
                _MiniPill(text: "Confidence $confidence"),
                _MiniPill(text: "Confidence level $confidenceLevel"),
                _MiniPill(text: "Cortisol proxy $cortisolProxy"),
              ],
            ),
          ),
          const SizedBox(height: 12),
          _CardSection(
            title: "How each value is computed",
            subtitle: "Tap info for technical definition",
            child: Column(
              children: [
                _ExplainTile(
                  title: "Stress score",
                  value: stressScore,
                  explanation:
                      "Stress score is the model output after calibration adjustment and smoothing. Smoothing uses exponential update: smooth_t = 0.7 * smooth_(t-1) + 0.3 * raw_t.",
                ),
                _ExplainTile(
                  title: "Confidence",
                  value: confidence,
                  explanation:
                      "Confidence blends baseline-relative sensor deviation confidence and model certainty. Sensor side uses HR, EDA, and Temp z-band levels weighted 0.4, 0.4, 0.2.",
                ),
                _ExplainTile(
                  title: "Confidence level",
                  value: confidenceLevel,
                  explanation:
                      "Confidence level is bucketed from confidence value: High >= 0.75, Medium >= 0.45, otherwise Low.",
                ),
                _ExplainTile(
                  title: "Cortisol proxy",
                  value: cortisolProxy,
                  explanation:
                      "Cortisol proxy is a non-medical trend value computed as stress_score * 100, clamped to [0,100]. It is not biochemical cortisol.",
                ),
                _ExplainTile(
                  title: "Inference window",
                  value: inferenceWindowText,
                  explanation:
                      "Inference window shows current buffered samples over required samples for feature extraction. It is not calibration progress.",
                ),
              ],
            ),
          ),
          const SizedBox(height: 12),
          _CardSection(
            title: "Calibration state",
            subtitle: "Personal baseline status",
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Wrap(
                  spacing: 8,
                  runSpacing: 8,
                  children: [
                    _MiniPill(text: calibrationReady ? "Calibrated" : "Uncalibrated"),
                    _MiniPill(text: "Valid samples $calibrationSamples (min $calibrationSampleMin)"),
                    _MiniPill(text: "Elapsed $calibrationElapsedText"),
                    _MiniPill(text: "Time left $calibrationRemainingText"),
                    _MiniPill(text: guidedCalibrationActive ? "Mode Calibrating" : "Mode Idle"),
                  ],
                ),
                const SizedBox(height: 10),
                Text(
                  stressInputIssue == null ? "All required signals are valid." : stressInputIssue!,
                ),
              ],
            ),
          ),
        ],
      ),
    );
  }
}

class _ExplainTile extends StatelessWidget {
  final String title;
  final String value;
  final String explanation;

  const _ExplainTile({
    required this.title,
    required this.value,
    required this.explanation,
  });

  @override
  Widget build(BuildContext context) {
    return ListTile(
      contentPadding: EdgeInsets.zero,
      title: Text(title),
      subtitle: Text(value),
      trailing: IconButton(
        icon: const Icon(Icons.info_outline),
        onPressed: () {
          showDialog<void>(
            context: context,
            builder: (ctx) => AlertDialog(
              title: Text(title),
              content: Text(explanation),
              actions: [
                TextButton(
                  onPressed: () => Navigator.of(ctx).pop(),
                  child: const Text("Close"),
                ),
              ],
            ),
          );
        },
      ),
    );
  }
}

class _MeasureSummary {
  final double score;
  final double confidence;
  final String level;
  final int validSamples;
  final int invalidSamples;

  const _MeasureSummary({
    required this.score,
    required this.confidence,
    required this.level,
    required this.validSamples,
    required this.invalidSamples,
  });
}

class _CardSection extends StatelessWidget {
  final String title;
  final String subtitle;
  final Widget child;

  const _CardSection({required this.title, required this.subtitle, required this.child});

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;
    return Card(
      child: Padding(
        padding: const EdgeInsets.all(14),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Text(title, style: const TextStyle(fontSize: 16, fontWeight: FontWeight.w600)),
            const SizedBox(height: 4),
            Text(subtitle, style: TextStyle(color: cs.onSurface.withValues(alpha: 0.7))),
            const SizedBox(height: 12),
            child,
          ],
        ),
      ),
    );
  }
}

class _DeviceTile extends StatelessWidget {
  final String name;
  final String id;
  final int rssi;
  final VoidCallback onTap;

  const _DeviceTile({required this.name, required this.id, required this.rssi, required this.onTap});

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;

    return InkWell(
      onTap: onTap,
      borderRadius: BorderRadius.circular(14),
      child: Container(
        margin: const EdgeInsets.only(bottom: 10),
        padding: const EdgeInsets.all(12),
        decoration: BoxDecoration(
          borderRadius: BorderRadius.circular(14),
          color: cs.surfaceContainerHighest.withValues(alpha: 0.22),
          border: Border.all(color: Colors.white.withValues(alpha: 0.08)),
        ),
        child: Row(
          children: [
            const Icon(Icons.devices),
            const SizedBox(width: 10),
            Expanded(
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  Text(name, style: const TextStyle(fontWeight: FontWeight.w700)),
                  const SizedBox(height: 3),
                  Text(
                    id,
                    style: TextStyle(color: Colors.white.withValues(alpha: 0.6), fontSize: 12),
                    maxLines: 1,
                    overflow: TextOverflow.ellipsis,
                  ),
                ],
              ),
            ),
            const SizedBox(width: 10),
            _MiniPill(text: "RSSI $rssi"),
            const SizedBox(width: 8),
            const Icon(Icons.chevron_right),
          ],
        ),
      ),
    );
  }
}

class _EmptyState extends StatelessWidget {
  final String text;
  const _EmptyState({required this.text});

  @override
  Widget build(BuildContext context) {
    return Container(
      padding: const EdgeInsets.all(14),
      decoration: BoxDecoration(
        borderRadius: BorderRadius.circular(14),
        border: Border.all(color: Colors.white.withValues(alpha: 0.08)),
      ),
      child: Row(
        children: [
          const Icon(Icons.info_outline),
          const SizedBox(width: 10),
          Expanded(child: Text(text)),
        ],
      ),
    );
  }
}

class _StatusPill extends StatelessWidget {
  final String text;
  const _StatusPill({required this.text});

  @override
  Widget build(BuildContext context) {
    return Container(
      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 6),
      decoration: BoxDecoration(
        borderRadius: BorderRadius.circular(999),
        color: Colors.white.withValues(alpha: 0.08),
        border: Border.all(color: Colors.white.withValues(alpha: 0.10)),
      ),
      child: Text(
        text,
        style: const TextStyle(fontSize: 12),
        maxLines: 1,
        overflow: TextOverflow.ellipsis,
      ),
    );
  }
}

class _MiniPill extends StatelessWidget {
  final String text;
  const _MiniPill({required this.text});

  @override
  Widget build(BuildContext context) {
    return Container(
      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 6),
      decoration: BoxDecoration(
        borderRadius: BorderRadius.circular(999),
        color: Colors.white.withValues(alpha: 0.06),
        border: Border.all(color: Colors.white.withValues(alpha: 0.10)),
      ),
      child: Text(text, style: const TextStyle(fontSize: 12)),
    );
  }
}

class HistoryEntry {
  final DateTime when;
  final int? ts;
  final double? bpmAvg;
  final double? gsrAvg;
  final double? tempAvg;
  final double stressProb;
  final double cortisolProxy;
  final String stressLevel;
  final String label;

  const HistoryEntry({
    required this.when,
    required this.ts,
    required this.bpmAvg,
    required this.gsrAvg,
    required this.tempAvg,
    required this.stressProb,
    required this.cortisolProxy,
    required this.stressLevel,
    required this.label,
  });
}

class _HistoryTable extends StatelessWidget {
  final List<HistoryEntry> entries;

  const _HistoryTable({required this.entries});

  @override
  Widget build(BuildContext context) {
    if (entries.isEmpty) {
      return const _EmptyState(text: "No history yet. Start receiving live data.");
    }

    final rows = entries.reversed.take(40).toList(growable: false);
    String fmt(double? v) => v == null ? "N/A" : v.toStringAsFixed(2);

    return SingleChildScrollView(
      scrollDirection: Axis.horizontal,
      child: DataTable(
        columns: const [
          DataColumn(label: Text("Time")),
          DataColumn(label: Text("ts")),
          DataColumn(label: Text("BPM")),
          DataColumn(label: Text("GSR")),
          DataColumn(label: Text("Temp")),
          DataColumn(label: Text("Stress %")),
          DataColumn(label: Text("Proxy")),
          DataColumn(label: Text("Level")),
          DataColumn(label: Text("Label")),
        ],
        rows: rows
            .map(
              (e) => DataRow(cells: [
                DataCell(Text("${e.when.hour.toString().padLeft(2, '0')}:${e.when.minute.toString().padLeft(2, '0')}:${e.when.second.toString().padLeft(2, '0')}")),
                DataCell(Text(e.ts?.toString() ?? "N/A")),
                DataCell(Text(fmt(e.bpmAvg))),
                DataCell(Text(fmt(e.gsrAvg))),
                DataCell(Text(fmt(e.tempAvg))),
                DataCell(Text((e.stressProb * 100).toStringAsFixed(1))),
                DataCell(Text(e.cortisolProxy.toStringAsFixed(1))),
                DataCell(Text(e.stressLevel)),
                DataCell(Text(e.label)),
              ]),
            )
            .toList(growable: false),
      ),
    );
  }
}

class _HistoryPage extends StatelessWidget {
  final List<HistoryEntry> entries;
  final String? csvPath;
  final int loggedRows;
  final Future<void> Function() onCopyCsv;

  const _HistoryPage({
    required this.entries,
    required this.csvPath,
    required this.loggedRows,
    required this.onCopyCsv,
  });

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text("Session History"),
        actions: [
          IconButton(
            tooltip: "Copy CSV",
            onPressed: onCopyCsv,
            icon: const Icon(Icons.copy),
          ),
          const SizedBox(width: 8),
        ],
      ),
      body: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          _CardSection(
            title: "Logger",
            subtitle: "Export and file information",
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                _MiniPill(text: "Logged rows $loggedRows"),
                const SizedBox(height: 8),
                Text("CSV path: ${csvPath ?? "N/A"}"),
                const SizedBox(height: 8),
                FilledButton.icon(
                  onPressed: onCopyCsv,
                  icon: const Icon(Icons.file_copy_outlined),
                  label: const Text("Copy CSV to clipboard"),
                ),
              ],
            ),
          ),
          const SizedBox(height: 12),
          _CardSection(
            title: "History table",
            subtitle: "Latest rows from this run",
            child: _HistoryTable(entries: entries),
          ),
        ],
      ),
    );
  }
}
