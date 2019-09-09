#include <assert.h>
#include <pthread.h>
#include "votingdefs.h"
#include "sbb.h"

extern osd_stream_buffer_handle_t xScannerStreamBuffer;

void sim_main_loop(void);

int main(int argc, char **argv)
{
    (void)argc;
    (void)argv;
    pthread_t main_thread;
    osd_sim_initialize();
    pthread_create(&main_thread, NULL, ballot_box_main_loop, NULL);
    sim_main_loop();
    return 0;
}

void sim_main_loop(void)
{
    const char *help =
        "==================================\n"  \
        "1 - Press and release CAST button\n"   \
        "2 - Press and release SPOIL button\n"  \
        "3 - Activate PAPER IN sensor\n"        \
        "4 - Deactivate PAPER IN sensor\n"      \
        "5 - Scan and send BARCODE\n"           \
        "6 - Quit\n"                            \
        "==================================\n";
    for(;;)
    {
        printf("%s", help);
        uint32_t choice;
        if (0 == scanf("%u", &choice))
            continue;
        printf("CHOICE: %u\n", choice);
        switch (choice) {
        default:
            break;
        case 1:
            osd_sim_cast_button_pressed();
            osd_msleep(100);
            osd_sim_cast_button_released();
            break;
        case 2:
            osd_sim_spoil_button_pressed();
            osd_msleep(100);
            osd_sim_spoil_button_released();
            break;
        case 3:
            osd_sim_paper_sensor_in_pressed();
            break;
        case 4:
            osd_sim_paper_sensor_in_released();
            break;
        case 5:
            osd_sim_barcode_input();
            break;
        case 6:
            return;
        }
    }
}
