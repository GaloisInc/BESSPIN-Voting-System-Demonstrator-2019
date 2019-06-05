/**
 * Smart Ballot Box Hardware API
 * based on sbb_hardware.lando
 */

#include <stdbool.h>
#include <stdint.h>

#define BARCODE_MAX_LENGTH 16


/**
 * component LEDButton
 */
struct LedButton {
  uint8_t id;
};

/**
 * component LEDButton
 * Is button pressed?
 */
bool is_button_pressed(struct LedButton *button);

/**
 * component LEDButton
 * Button Light On!
 */
void button_light_on(struct LedButton *button);

/**
 * component LEDButton
 * Button Light Off!
 */
void button_light_off(struct LedButton *button);

/**
 * component Paper Sensor
 */
struct PaperSensor {
  uint8_t id;
};

/**
 * component Paper Sensor
 * Paper detected ?
 */
bool is_paper_detected(struct PaperSensor *sensor);


/**
 * component Ballot Box
 */
struct BallotBox {
    struct BarcodeScanner *scanner;
    struct LedButton buttons[2];
    struct PaperSensor sensors[2];
};

/**
 * component Ballot Box
 * Deposit ballot!
 */
void deposit_ballot(void);

/**
 * component Barcode Scanner
 */
struct BarcodeScanner {
  bool has_barcode;
  char barcode[BARCODE_MAX_LENGTH];
};

/**
 * component Barcode Scanner
 * Has a valid barcode?
 */
bool has_a_valid_bardcode(struct BarcodeScanner * sensor);

/**
 * component Barcode Scanner
 * What is the barcode?
 */
void what_is_the_barcode(struct BarcodeScanner * sensor, char *str, uint8_t len);


/**
 * component Motor
 * Motor Forward!
 */
void motor_forward(void);

/**
 * component Motor
 * Motor Backward!
 */
void motor_backward(void);

/**
 * component Motor
 * Motor Stop!
 */
void motor_stop(void);

/**
 * component LCD Display
 * Display this text!
 */
void display_this_text(char *str, uint8_t len);

