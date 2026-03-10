// Put this first so Arduino auto generated prototypes can see Stats
struct Stats {
  float avg;
  float mn;
  float mx;
  float sd;
  bool valid;
};

/*************************************************************
  ESP32: BLE + OLED + MAX30102 + MAX30205 + GSR

  Behavior
  1) Device stays in deep sleep by default
  2) Wake on external button press
  3) BLE advertises and waits up to 60 seconds for phone connection
  4) If connected, start a 5-minute active session
  5) Sample BPM, Temp, GSR every 1 second
  6) Collect 10 samples, compute avg/min/max/std, and send every 10 seconds
  7) If button is pressed during active session, extend by +5 minutes
  8) On disconnect / timeout / session end, return to deep sleep

  Fixes included
  - Proper deep-sleep wake on GPIO33
  - MAX30102 processing limited per loop so BLE is not starved
  - Reduced serial logging rate
  - Lower MAX30102 LED current
  - Lower no-finger threshold
  - BLE notify debug prints
*************************************************************/

#include <math.h>

#include <Wire.h>
#include "MAX30105.h"
#include "heartRate.h"
#include "ClosedCube_MAX30205.h"

#include <SPI.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>

#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>
#include <BLESecurity.h>

#include <esp_gap_ble_api.h>
#include <esp_gatt_defs.h>
#include <esp_sleep.h>
#include <esp_system.h>
#include <driver/rtc_io.h>

// -------------------- Forward declarations --------------------
void prepareWakeButton();
void enterDeepSleep(const char* reason);
bool consumeButtonPressEvent();

void oledPrintStatus(const String& a, const String& b = "", const String& c = "");
void oledShowPairingPinLarge(uint32_t pin, bool connected);
void updateOLEDStats(float bpmAvg, float tempAvg, float gsrAvg);
void oledShowStressResult(const char* level, float score, float confidence);

int readGsrAverage();
void setupBLE();
void checkBleHeartbeatTimeout();
void ensureBleAdvertisingAlive();
void logBleStatusIfNeeded();

Stats computeStats(const float* x, int n);
Stats computeStatsTempIgnoreNaN(const float* x, int n);
void bleSendStatsJSON(uint32_t tsMs, const Stats& b, const Stats& t, const Stats& g);
void sampleEvery1s();
void processBleEvents();
void refreshPairingScreenIfNeeded();
void refreshResultScreenIfNeeded();

uint8_t findMAX30205Addr();
void forceBleDisconnect(const char* reason);

// -------------------- I2C pins --------------------
#define SDA_PIN 21
#define SCL_PIN 22

// -------------------- GSR --------------------
#define GSR_PIN 34

// -------------------- Wake / session button --------------------
#define WAKE_BUTTON_PIN 33   // button to GND

// -------------------- MAX30102 --------------------
MAX30105 particleSensor;
bool max30102_ok = false;

const byte RATE_SIZE = 4;
byte rates[RATE_SIZE] = {0, 0, 0, 0};
byte rateSpot = 0;
long lastBeat = 0;
float beatsPerMinute = 0;
int beatAvg = 0;

static const long IR_NO_FINGER_THRESHOLD = 5000;
static const uint8_t MAX30102_LED_RED = 0x10;
static const uint8_t MAX30102_LED_IR  = 0x10;
static const int MAX_SAMPLES_PER_LOOP = 4;

// -------------------- MAX30205 --------------------
ClosedCube_MAX30205 max30205;
bool max30205_ok = false;
uint8_t max30205Addr = 0;

float TEMP_OFFSET_C = 0.0f;

// -------------------- OLED (SPI) --------------------
#define SCREEN_WIDTH 128
#define SCREEN_HEIGHT 64

#define OLED_MOSI   23
#define OLED_CLK    18
#define OLED_DC     16
#define OLED_CS     5
#define OLED_RESET  4

Adafruit_SSD1306 display(
  SCREEN_WIDTH, SCREEN_HEIGHT,
  OLED_MOSI, OLED_CLK, OLED_DC, OLED_RESET, OLED_CS
);

bool oled_ok = false;

// -------------------- BLE SETUP --------------------
#define BLE_DEVICE_NAME     "ESP32_HealthMonitor"
#define SERVICE_UUID        "12345678-1234-1234-1234-1234567890ab"
#define CHAR_UUID_NOTIFY    "abcd1234-5678-1234-5678-abcdef123456"
#define CHAR_UUID_HEARTBEAT "abcd1234-5678-1234-5678-abcdef123457"

BLEServer* pServer = nullptr;
BLECharacteristic* pChar = nullptr;
BLECharacteristic* pHeartbeatChar = nullptr;
volatile bool bleClientConnected = false;
volatile uint32_t lastHeartbeatMs = 0;
volatile bool evtHeartbeatTimeout = false;
static const uint32_t HEARTBEAT_TIMEOUT_MS = 30000;
volatile uint32_t lastAdvKickMs = 0;
static const uint32_t ADV_WATCHDOG_MS = 5000;
volatile uint32_t lastStatusLogMs = 0;
static const uint32_t STATUS_LOG_MS = 5000;
volatile bool evtResultReady = false;
char pendingResultLevel[16] = "N/A";
volatile float pendingResultScore = 0.0f;
volatile float pendingResultConfidence = 0.0f;
bool resultScreenActive = false;
uint32_t resultScreenUntilMs = 0;
char resultLevel[16] = "N/A";
float resultScore = 0.0f;
float resultConfidence = 0.0f;
static const uint32_t RESULT_SHOW_MS = 15000;
static const uint32_t SAMPLE_INTERVAL_MS = 1000;
uint32_t lastSampleMs = 0;

// -------------------- Session state machine --------------------
enum DeviceState {
  STATE_CONNECT,
  STATE_ACTIVE_SESSION
};

DeviceState deviceState = STATE_CONNECT;
uint32_t connectDeadlineMs = 0;
uint32_t sessionDeadlineMs = 0;

static const uint32_t CONNECT_TIMEOUT_MS    = 60000;
static const uint32_t SESSION_WINDOW_MS     = 300000;
static const uint32_t SESSION_EXTENSION_MS  = 300000;
static const bool START_ACTIVE_ON_COLD_BOOT = false;

volatile bool evtButtonPressed = false;

// Dynamic passkey
static uint32_t BLE_PASSKEY = 0;

// ---- Deferred BLE events ----
volatile bool evtBleConnected = false;
volatile bool evtBleDisconnected = false;
volatile bool evtAuthSuccess = false;
volatile bool evtAuthFail = false;
volatile bool evtPasskeyShow = false;
volatile uint32_t evtPasskey = 0;

// ---- Pairing UI state ----
volatile bool pairingPinActive = false;
volatile uint32_t pairingPinValue = 0;
volatile uint32_t pairingPinUntilMs = 0;
static const uint32_t PIN_SHOW_MS = 120000;

// -------------------- Sampling buffers --------------------
static const int WIN = 10;  // sample every 1s, send aggregated stats every 10 samples

float bpmBuf[WIN];
float tempBuf[WIN];
float gsrBuf[WIN];
int sampleCount = 0;

// -------------------- Interrupt --------------------
void IRAM_ATTR onSessionButtonPress() {
  evtButtonPressed = true;
}

bool consumeButtonPressEvent() {
  static uint32_t lastAcceptedMs = 0;
  if (!evtButtonPressed) return false;

  evtButtonPressed = false;

  uint32_t now = millis();
  if ((uint32_t)(now - lastAcceptedMs) < 250) return false;

  lastAcceptedMs = now;
  return true;
}

void prepareWakeButton() {
  pinMode(WAKE_BUTTON_PIN, INPUT_PULLUP);
  detachInterrupt(digitalPinToInterrupt(WAKE_BUTTON_PIN));
  attachInterrupt(digitalPinToInterrupt(WAKE_BUTTON_PIN), onSessionButtonPress, FALLING);
}

void enterDeepSleep(const char* reason) {
  Serial.print("Entering deep sleep: ");
  Serial.println(reason);

  if (oled_ok) oledPrintStatus("SLEEP", reason, "Press button to wake");

  delay(120);
  BLEDevice::deinit(false);

  rtc_gpio_deinit((gpio_num_t)WAKE_BUTTON_PIN);
  rtc_gpio_init((gpio_num_t)WAKE_BUTTON_PIN);
  rtc_gpio_set_direction((gpio_num_t)WAKE_BUTTON_PIN, RTC_GPIO_MODE_INPUT_ONLY);
  rtc_gpio_pullup_en((gpio_num_t)WAKE_BUTTON_PIN);
  rtc_gpio_pulldown_dis((gpio_num_t)WAKE_BUTTON_PIN);

  esp_sleep_enable_ext0_wakeup((gpio_num_t)WAKE_BUTTON_PIN, 0);
  delay(50);
  esp_deep_sleep_start();
}

static uint32_t genPasskey6() {
  return 100000u + (esp_random() % 900000u);
}

uint8_t findMAX30205Addr() {
  for (uint8_t a = 0x48; a <= 0x4F; a++) {
    Wire.beginTransmission(a);
    if (Wire.endTransmission() == 0) return a;
  }
  return 0;
}

// -------------------- OLED helpers --------------------
void oledPrintStatus(const String& a, const String& b, const String& c) {
  if (!oled_ok) return;

  display.clearDisplay();
  display.setTextColor(SSD1306_WHITE);
  display.setTextSize(1);
  display.setCursor(0, 0);
  display.println(a);
  if (b.length()) display.println(b);
  if (c.length()) display.println(c);
  display.display();
}

void oledShowPairingPinLarge(uint32_t pin, bool connected) {
  if (!oled_ok) return;

  display.clearDisplay();
  display.setTextColor(SSD1306_WHITE);

  display.setTextSize(1);
  display.setCursor(0, 0);
  display.print("BLE Pairing PIN");

  display.setTextSize(3);
  display.setCursor(8, 20);
  char pinBuf[7];
  snprintf(pinBuf, sizeof(pinBuf), "%06lu", (unsigned long)pin);
  display.print(pinBuf);

  display.setTextSize(1);
  display.setCursor(0, 56);
  display.print(connected ? "Connected: enter PIN" : "Waiting for phone...");
  display.display();
}

void updateOLEDStats(float bpmAvg, float tempAvg, float gsrAvg) {
  if (!oled_ok) return;
  if (pairingPinActive) return;
  if (resultScreenActive) return;

  display.clearDisplay();
  display.setTextColor(SSD1306_WHITE);

  display.setTextSize(2);
  display.setCursor(0, 0);
  display.print("B:");
  display.print((int)(bpmAvg + 0.5f));

  display.setTextSize(1);
  display.setCursor(0, 28);
  display.print("T: ");
  if (isnan(tempAvg)) display.print("N/A");
  else display.print(tempAvg, 1);
  display.print(" C");

  display.setCursor(0, 44);
  display.print("G: ");
  display.print((int)(gsrAvg + 0.5f));

  display.setCursor(92, 44);
  display.print("--");

  display.display();
}

void oledShowStressResult(const char* level, float score, float confidence) {
  if (!oled_ok) return;

  display.clearDisplay();
  display.setTextColor(SSD1306_WHITE);

  display.setTextSize(1);
  display.setCursor(0, 0);
  display.print("Stress Result");

  display.setCursor(0, 16);
  display.print("Level: ");
  display.print(level);

  display.setCursor(0, 32);
  display.print("Score: ");
  display.print(score, 3);

  display.setCursor(0, 48);
  display.print("Conf: ");
  display.print((int)(confidence * 100.0f + 0.5f));
  display.print("%");

  display.display();
}

// -------------------- GSR average --------------------
int readGsrAverage() {
  long sum = 0;
  for (int i = 0; i < 5; i++) {
    sum += analogRead(GSR_PIN);
    delay(1);
  }
  return (int)(sum / 5);
}

// -------------------- BLE callbacks --------------------
class MySecurityCallbacks : public BLESecurityCallbacks {
  uint32_t onPassKeyRequest() override {
    BLE_PASSKEY = genPasskey6();
    evtPasskey = BLE_PASSKEY;
    evtPasskeyShow = true;
    return BLE_PASSKEY;
  }

  void onPassKeyNotify(uint32_t pass_key) override {
    evtPasskey = pass_key;
    evtPasskeyShow = true;
  }

  bool onConfirmPIN(uint32_t pass_key) override {
    Serial.print("Confirm passkey: ");
    Serial.println(pass_key);
    return true;
  }

  bool onSecurityRequest() override {
    return true;
  }

  void onAuthenticationComplete(esp_ble_auth_cmpl_t auth_cmpl) override {
    if (!auth_cmpl.success) {
      evtAuthFail = true;
      return;
    }
    evtAuthSuccess = true;
  }
};

class MyServerCallbacks : public BLEServerCallbacks {
  void onConnect(BLEServer* server) override {
    (void)server;
    bleClientConnected = true;
    lastHeartbeatMs = millis();
    evtBleConnected = true;
  }

  void onDisconnect(BLEServer* server) override {
    (void)server;
    bleClientConnected = false;
    evtBleDisconnected = true;
    BLEDevice::startAdvertising();
  }
};

void forceBleDisconnect(const char* reason) {
  if (!pServer) return;

  uint16_t connId = pServer->getConnId();
  Serial.print("Forcing BLE disconnect: ");
  Serial.println(reason);
  pServer->disconnect(connId);
}

class HeartbeatCallbacks : public BLECharacteristicCallbacks {
  void onWrite(BLECharacteristic* characteristic) override {
    if (!characteristic) return;

    String value = characteristic->getValue();
    lastHeartbeatMs = millis();

    if (value.startsWith("RESULT|")) {
      int p1 = value.indexOf('|');
      int p2 = value.indexOf('|', p1 + 1);
      int p3 = value.indexOf('|', p2 + 1);

      if (p1 >= 0 && p2 > p1 && p3 > p2) {
        String lvl = value.substring(p1 + 1, p2);
        String scoreStr = value.substring(p2 + 1, p3);
        String confStr = value.substring(p3 + 1);

        if (lvl.length() == 0) lvl = "N/A";
        lvl.toCharArray(pendingResultLevel, sizeof(pendingResultLevel));
        pendingResultScore = scoreStr.toFloat();
        pendingResultConfidence = confStr.toFloat();
        evtResultReady = true;
        Serial.println("BLE stress result received");
      }
      return;
    }

    Serial.print("BLE heartbeat received: ");
    Serial.println(value);

    if (value == "RESET") {
      forceBleDisconnect("remote reset request");
    }
  }
};

void setupBLE() {
  BLEDevice::setMTU(185);
  BLEDevice::init(BLE_DEVICE_NAME);

  BLESecurity* security = new BLESecurity();
  security->setAuthenticationMode(ESP_LE_AUTH_REQ_SC_MITM_BOND);
  security->setCapability(ESP_IO_CAP_OUT);
  security->setInitEncryptionKey(ESP_BLE_ENC_KEY_MASK | ESP_BLE_ID_KEY_MASK);
  security->setRespEncryptionKey(ESP_BLE_ENC_KEY_MASK | ESP_BLE_ID_KEY_MASK);
  security->setKeySize(16);

  BLEDevice::setSecurityCallbacks(new MySecurityCallbacks());

  pServer = BLEDevice::createServer();
  pServer->setCallbacks(new MyServerCallbacks());

  BLEService* pService = pServer->createService(SERVICE_UUID);

  pChar = pService->createCharacteristic(
    CHAR_UUID_NOTIFY,
    BLECharacteristic::PROPERTY_READ |
    BLECharacteristic::PROPERTY_NOTIFY
  );

  pChar->setAccessPermissions(ESP_GATT_PERM_READ_ENC_MITM);
  pChar->addDescriptor(new BLE2902());
  pChar->setValue("Booting...");

  pHeartbeatChar = pService->createCharacteristic(
    CHAR_UUID_HEARTBEAT,
    BLECharacteristic::PROPERTY_WRITE |
    BLECharacteristic::PROPERTY_WRITE_NR
  );

  pHeartbeatChar->setAccessPermissions(ESP_GATT_PERM_WRITE_ENC_MITM);
  pHeartbeatChar->setCallbacks(new HeartbeatCallbacks());

  pService->start();

  BLEAdvertising* adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(SERVICE_UUID);
  adv->setScanResponse(true);
  adv->start();
  lastAdvKickMs = millis();

  Serial.println("BLE advertising started");
}

void checkBleHeartbeatTimeout() {
  if (!bleClientConnected) return;

  uint32_t now = millis();
  if ((uint32_t)(now - lastHeartbeatMs) <= HEARTBEAT_TIMEOUT_MS) return;

  evtHeartbeatTimeout = true;
  Serial.println("BLE heartbeat timeout");
  forceBleDisconnect("heartbeat timeout");
  lastHeartbeatMs = now;
}

void ensureBleAdvertisingAlive() {
  if (bleClientConnected) return;

  uint32_t now = millis();
  if ((uint32_t)(now - lastAdvKickMs) < ADV_WATCHDOG_MS) return;

  lastAdvKickMs = now;
  BLEDevice::stopAdvertising();
  delay(20);
  BLEDevice::startAdvertising();
  Serial.println("BLE advertising watchdog restart");
}

void logBleStatusIfNeeded() {
  uint32_t now = millis();
  if ((uint32_t)(now - lastStatusLogMs) < STATUS_LOG_MS) return;

  lastStatusLogMs = now;
  Serial.print("BLE status connected=");
  Serial.print(bleClientConnected ? "1" : "0");
  Serial.print(" hbAgeMs=");
  Serial.print((unsigned long)(now - lastHeartbeatMs));
  Serial.print(" advKickAgeMs=");
  Serial.println((unsigned long)(now - lastAdvKickMs));
}

// -------------------- Stats helpers --------------------
Stats computeStats(const float* x, int n) {
  Stats s;
  s.valid = (n > 0);

  if (!s.valid) {
    s.avg = NAN;
    s.mn = NAN;
    s.mx = NAN;
    s.sd = NAN;
    return s;
  }

  float sum = 0.0f;
  float mn = x[0];
  float mx = x[0];

  for (int i = 0; i < n; i++) {
    sum += x[i];
    if (x[i] < mn) mn = x[i];
    if (x[i] > mx) mx = x[i];
  }

  float avg = sum / (float)n;

  float varSum = 0.0f;
  for (int i = 0; i < n; i++) {
    float d = x[i] - avg;
    varSum += d * d;
  }

  float variance = varSum / (float)n;
  float sd = sqrtf(variance);

  s.avg = avg;
  s.mn = mn;
  s.mx = mx;
  s.sd = sd;
  return s;
}

Stats computeStatsTempIgnoreNaN(const float* x, int n) {
  float tmp[WIN];
  int m = 0;

  for (int i = 0; i < n; i++) {
    if (!isnan(x[i])) tmp[m++] = x[i];
  }

  if (m == 0) {
    Stats s;
    s.valid = false;
    s.avg = NAN;
    s.mn = NAN;
    s.mx = NAN;
    s.sd = NAN;
    return s;
  }

  return computeStats(tmp, m);
}

// -------------------- BLE send stats --------------------
void bleSendStatsJSON(uint32_t tsMs, const Stats& b, const Stats& t, const Stats& g) {
  if (!pChar) return;

  char buf[340];
  int n = 0;

  if (!t.valid) {
    n = snprintf(
      buf, sizeof(buf),
      "{"
      "\"ts\":%lu,"
      "\"BPM\":{\"avg\":%.2f,\"min\":%.2f,\"max\":%.2f,\"std\":%.2f},"
      "\"GSR\":{\"avg\":%.2f,\"min\":%.2f,\"max\":%.2f,\"std\":%.2f},"
      "\"Temp\":{\"avg\":null,\"min\":null,\"max\":null,\"std\":null}"
      "}",
      (unsigned long)tsMs,
      b.avg, b.mn, b.mx, b.sd,
      g.avg, g.mn, g.mx, g.sd
    );
  } else {
    n = snprintf(
      buf, sizeof(buf),
      "{"
      "\"ts\":%lu,"
      "\"BPM\":{\"avg\":%.2f,\"min\":%.2f,\"max\":%.2f,\"std\":%.2f},"
      "\"GSR\":{\"avg\":%.2f,\"min\":%.2f,\"max\":%.2f,\"std\":%.2f},"
      "\"Temp\":{\"avg\":%.2f,\"min\":%.2f,\"max\":%.2f,\"std\":%.2f}"
      "}",
      (unsigned long)tsMs,
      b.avg, b.mn, b.mx, b.sd,
      g.avg, g.mn, g.mx, g.sd,
      t.avg, t.mn, t.mx, t.sd
    );
  }

  if (n <= 0 || n >= (int)sizeof(buf)) return;

  Serial.println("Sending BLE JSON:");
  Serial.println(buf);

  pChar->setValue((uint8_t*)buf, (size_t)n);

  if (bleClientConnected) {
    pChar->notify();
    Serial.println("notify() called");
  }
}

// -------------------- Sampling --------------------
void sampleEvery1s() {
  float tempC = NAN;
  if (max30205_ok) tempC = max30205.readTemperature() + TEMP_OFFSET_C;

  float bpmNow = (float)beatAvg;
  float gsrNow = (float)readGsrAverage();

  bpmBuf[sampleCount]  = bpmNow;
  tempBuf[sampleCount] = tempC;
  gsrBuf[sampleCount]  = gsrNow;

  sampleCount++;

  if (sampleCount >= WIN) {
    Stats b = computeStats(bpmBuf, WIN);
    Stats g = computeStats(gsrBuf, WIN);
    Stats t = computeStatsTempIgnoreNaN(tempBuf, WIN);

    uint32_t tsMs = millis();

    updateOLEDStats(b.avg, t.valid ? t.avg : NAN, g.avg);
    bleSendStatsJSON(tsMs, b, t, g);

    sampleCount = 0;
  }
}

// -------------------- Deferred BLE event processing --------------------
void processBleEvents() {
  if (evtPasskeyShow) {
    evtPasskeyShow = false;
    pairingPinValue = evtPasskey;
    pairingPinActive = true;
    pairingPinUntilMs = millis() + PIN_SHOW_MS;

    Serial.print("BLE Passkey: ");
    Serial.println((unsigned long)pairingPinValue);
    oledShowPairingPinLarge(pairingPinValue, bleClientConnected);
  }

  if (evtBleConnected) {
    evtBleConnected = false;
    Serial.println("BLE connected");
    if (pairingPinActive) {
      oledShowPairingPinLarge(pairingPinValue, true);
    } else if (oled_ok) {
      oledPrintStatus("BLE connected", "Pair now on phone", "Use shown PIN");
    }
  }

  if (evtBleDisconnected) {
    evtBleDisconnected = false;
    pairingPinActive = false;
    lastAdvKickMs = millis();
    Serial.println("BLE disconnected");
    if (oled_ok) oledPrintStatus("BLE disconnected", "Advertising...");
  }

  if (evtAuthSuccess) {
    evtAuthSuccess = false;
    pairingPinActive = false;
    Serial.println("BLE auth success (bonded)");
    if (oled_ok) oledPrintStatus("BLE bonded", "Encrypted link");
  }

  if (evtAuthFail) {
    evtAuthFail = false;
    pairingPinActive = false;
    Serial.println("BLE auth failed");
    if (oled_ok) oledPrintStatus("BLE auth failed");
  }

  if (evtHeartbeatTimeout) {
    evtHeartbeatTimeout = false;
    if (oled_ok) oledPrintStatus("BLE timeout", "Restarting advertise");
  }

  if (evtResultReady) {
    evtResultReady = false;
    strncpy(resultLevel, pendingResultLevel, sizeof(resultLevel) - 1);
    resultLevel[sizeof(resultLevel) - 1] = '\0';
    resultScore = pendingResultScore;
    resultConfidence = pendingResultConfidence;
    resultScreenActive = true;
    resultScreenUntilMs = millis() + RESULT_SHOW_MS;
    oledShowStressResult(resultLevel, resultScore, resultConfidence);
  }
}

void refreshPairingScreenIfNeeded() {
  if (!pairingPinActive) return;

  if ((int32_t)(millis() - pairingPinUntilMs) >= 0) {
    pairingPinActive = false;
    return;
  }

  static uint32_t lastPaint = 0;
  if (millis() - lastPaint > 500) {
    lastPaint = millis();
    oledShowPairingPinLarge(pairingPinValue, bleClientConnected);
  }
}

void refreshResultScreenIfNeeded() {
  if (!resultScreenActive) return;

  if ((int32_t)(millis() - resultScreenUntilMs) >= 0) {
    resultScreenActive = false;
    return;
  }

  static uint32_t lastPaint = 0;
  if (millis() - lastPaint > 500) {
    lastPaint = millis();
    oledShowStressResult(resultLevel, resultScore, resultConfidence);
  }
}

void setup() {
  Serial.begin(115200);
  delay(300);

  prepareWakeButton();

  esp_sleep_wakeup_cause_t wakeupCause = esp_sleep_get_wakeup_cause();
  Serial.print("Wakeup cause: ");
  Serial.println((int)wakeupCause);

  bool wokeFromButton = (wakeupCause == ESP_SLEEP_WAKEUP_EXT0);

  if (!wokeFromButton && !START_ACTIVE_ON_COLD_BOOT) {
    delay(80);
    enterDeepSleep("Wait wake button");
  }

  Serial.println("Init OLED...");
  oled_ok = display.begin(SSD1306_SWITCHCAPVCC);
  if (oled_ok) oledPrintStatus("OLED OK", "Booting...");
  else Serial.println("OLED init FAILED.");

  setupBLE();
  if (oled_ok) oledPrintStatus("BLE Advertising", BLE_DEVICE_NAME, "Pair from phone");

  Wire.begin(SDA_PIN, SCL_PIN);
  Wire.setClock(100000);

  analogReadResolution(12);
  analogSetAttenuation(ADC_11db);

  Serial.println("Init MAX30102...");
  if (oled_ok) oledPrintStatus("Init MAX30102...");

  max30102_ok = particleSensor.begin(Wire);
  if (!max30102_ok) {
    Serial.println("MAX30102 FAILED. Continuing without BPM.");
    if (oled_ok) oledPrintStatus("MAX30102 FAIL", "BPM will be 0");
  } else {
    particleSensor.setup(0x1F, 4, 2, 100, 411, 4096);
    particleSensor.setPulseAmplitudeRed(MAX30102_LED_RED);
    particleSensor.setPulseAmplitudeIR(MAX30102_LED_IR);
    particleSensor.setPulseAmplitudeGreen(0x00);
    Serial.println("MAX30102 OK.");
    if (oled_ok) oledPrintStatus("MAX30102 OK", "Red LED should be ON");
  }

  Serial.println("Scan MAX30205...");
  if (oled_ok) oledPrintStatus("Scan MAX30205...");

  max30205Addr = findMAX30205Addr();
  if (max30205Addr == 0) {
    Serial.println("MAX30205 not found. Temp will be N/A.");
    max30205_ok = false;
    if (oled_ok) oledPrintStatus("MAX30205 NOT FOUND", "Temp = N/A");
  } else {
    max30205.begin(max30205Addr);
    max30205_ok = true;
    Serial.print("MAX30205 found at 0x");
    if (max30205Addr < 16) Serial.print("0");
    Serial.println(max30205Addr, HEX);
    if (oled_ok) oledPrintStatus("MAX30205 OK", "Addr: 0x" + String(max30205Addr, HEX));
  }

  lastSampleMs = millis();
  connectDeadlineMs = millis() + CONNECT_TIMEOUT_MS;
  sessionDeadlineMs = 0;
  deviceState = STATE_CONNECT;

  if (oled_ok) {
    oledPrintStatus("WAIT CONNECT", "BLE advertising", "Connect in 60s");
  }
}

void loop() {
  uint32_t now = millis();

  bool buttonPressed = consumeButtonPressEvent();

  if (buttonPressed && deviceState == STATE_ACTIVE_SESSION) {
    sessionDeadlineMs += SESSION_EXTENSION_MS;
    Serial.println("Session extension requested (+5 min)");
    if (oled_ok) oledPrintStatus("SESSION EXTENDED", "+5 minutes", "Continue sampling");
  }

  processBleEvents();
  refreshPairingScreenIfNeeded();
  refreshResultScreenIfNeeded();

  if (deviceState == STATE_CONNECT) {
    if (bleClientConnected) {
      deviceState = STATE_ACTIVE_SESSION;
      sessionDeadlineMs = now + SESSION_WINDOW_MS;
      sampleCount = 0;
      lastSampleMs = now;
      Serial.println("Connected -> Active session started (5 min)");
      if (oled_ok) oledPrintStatus("SESSION ACTIVE", "Sampling + send", "Window: 5 min");
    } else if ((int32_t)(now - connectDeadlineMs) >= 0) {
      enterDeepSleep("Connect timeout");
    }
  } else if (deviceState == STATE_ACTIVE_SESSION) {
    if (!bleClientConnected) {
      enterDeepSleep("BLE disconnected");
    }

    if ((uint32_t)(now - lastSampleMs) >= SAMPLE_INTERVAL_MS) {
      lastSampleMs += SAMPLE_INTERVAL_MS;
      sampleEvery1s();
    }

    if ((int32_t)(now - sessionDeadlineMs) >= 0) {
      enterDeepSleep("Session complete");
    }
  }

  checkBleHeartbeatTimeout();
  ensureBleAdvertisingAlive();
  logBleStatusIfNeeded();

  if (max30102_ok) {
    particleSensor.check();

    int processed = 0;
    while (particleSensor.available() && processed < MAX_SAMPLES_PER_LOOP) {
      long irValue = particleSensor.getIR();
      particleSensor.nextSample();
      processed++;

      if (checkForBeat(irValue)) {
        long delta = millis() - lastBeat;
        lastBeat = millis();

        if (delta > 0) {
          beatsPerMinute = 60.0f / (delta / 1000.0f);

          if (beatsPerMinute > 20 && beatsPerMinute < 255) {
            rates[rateSpot++] = (byte)beatsPerMinute;
            rateSpot %= RATE_SIZE;

            int sumRates = 0;
            int validRates = 0;
            for (byte i = 0; i < RATE_SIZE; i++) {
              if (rates[i] > 0) {
                sumRates += rates[i];
                validRates++;
              }
            }

            if (validRates > 0) {
              beatAvg = sumRates / validRates;
            }
          }
        }
      }

      if (irValue < IR_NO_FINGER_THRESHOLD) {
        beatAvg = 0;
      }

      static uint32_t lastBpmLogMs = 0;
      if (millis() - lastBpmLogMs >= 500) {
        lastBpmLogMs = millis();
        Serial.print("IR=");
        Serial.print(irValue);
        Serial.print(" BPM=");
        Serial.println(beatAvg);
      }
    }
  } else {
    beatAvg = 0;
  }

  delay(5);
}
