#include <Wire.h>
#include <SPI.h>
#include <SD.h>
#include <RTCx.h>
#include <SerLCD.h> //Click here to get the library: http://librarymanager/All#SparkFun_SerLCD

#define CS 10
#define CAST_BTN 3
#define SPOIL_BTN 5
#define CAST_LED 2
#define SPOIL_LED 4

SerLCD lcd; // Initialize the library with default I2C address 0x72

void setup() {
  Serial.begin(9600);
  Wire.begin();
  Serial.println();
  lcd.begin(Wire);

  pinMode(SPOIL_BTN, INPUT);
  pinMode(CAST_BTN, INPUT);
  pinMode(SPOIL_LED, OUTPUT);
  pinMode(CAST_LED, OUTPUT);
  pinMode(CS, OUTPUT);

  //By default .begin() will set I2C SCL to Standard Speed mode of 100kHz
  Wire.setClock(400000); //Optional - set I2C SCL to High Speed Mode of 400kHz

  lcd.setBacklight(0xFF8C00); //orange
  lcd.clear();

  if (!rtc.autoprobe()) {
    Serial.println("No RTCx found, cannot continue");
    lcd.print("RTC Error");
    while (1)
      ;
  }

  // see if the card is present and can be initialized:
  if (!SD.begin(CS)) {
    Serial.println("Card failed, or not present");
    lcd.print("SD Failure");
    // don't do anything more:
    while (1);
  }
  
  rtc.enableBatteryBackup();
  rtc.startClock();
  rtc.setSQW(RTCx::freq32768Hz);


  digitalWrite(CAST_LED, HIGH);
  digitalWrite(SPOIL_LED, HIGH);
  digitalWrite(CS, HIGH);
}

char time_buffer[20];

void log(char *data) {
    struct RTCx::tm tm;
    rtc.readClock(tm);
    RTCx::isotime(&tm, time_buffer, sizeof(time_buffer));
    File logfile = SD.open('system-check.txt', FILE_WRITE);
    if(logfile) {
      logfile.print(time_buffer);
      logfile.print(" ");
      logfile.println(data);
      logfile.flush();
      logfile.close();
      Serial.print(time_buffer);
      Serial.print(" ");
      Serial.println(data);
    } else {
      Serial.println("Error opening system-check.txt log");
    }
}

unsigned long last_time = 0;
bool last_cast_state = 0;
bool last_spoil_state = 0;
void loop() {


  if(digitalRead(SPOIL_BTN)) {
    if(!last_spoil_state) {
      // State Changed from OFF to ON
      lcd.clear();
      log("SPOIL BUTTON DOWN");
      delay(100);
     }
    last_spoil_state = 1;
    return;
  } else {
      // State changed from ON to OFF  
      log("SPOIL BUTTON UP");
      delay(100);
      // TODO: Log state change
      last_spoil_state = 0;
    }
  
  if(digitalRead(CAST_BTN)) {
    if(!last_cast_state) {
     lcd.clear();
     log("CAST BUTTON UP");
     delay(100);
    }
    last_cast_state = 1;
    return;
  } else {
     log("CAST BUTTON UP");
     delay(100);
     last_cast_state = 0;
    }

  struct RTCx::tm tm;
  if (millis() - last_time > 1000) {
    lcd.clear();
    last_time = millis();
    rtc.readClock(tm);

    RTCx::isotime(&tm, time_buffer, sizeof(time_buffer));
    lcd.print(time_buffer);
    RTCx::time_t t = RTCx::mktime(&tm);
  }
  
}
