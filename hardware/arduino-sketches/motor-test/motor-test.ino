/*
 * 
 * Runs the motor driver in forward and reverse to test
 * motor functionality.
 * 
 */

void setup() {
  // put your setup code here, to run once:

  pinMode(7, OUTPUT);
  pinMode(6, OUTPUT);
  digitalWrite(6, LOW);
  digitalWrite(7, LOW);
}

void loop() {
  // put your main code here, to run repeatedly:
  digitalWrite(6, HIGH);
  digitalWrite(7, LOW);
  delay(5000);
  digitalWrite(7, HIGH);
  digitalWrite(6, LOW);
  delay(5000);
}
