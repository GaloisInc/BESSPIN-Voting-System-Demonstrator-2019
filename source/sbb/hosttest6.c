#include <assert.h>
#include "log.h"
#include "log_io.h"
#include "sbb_logging.h"

const log_name system_log_file_name = "sbb_test_system_hosttest6.log";
const log_name app_log_file_name = "sbb_test_app_hosttest6.log";

int main(int argc, char **argv) {
    char barcode[] = "A Barcode";
    char another_barcode[] = "Another Barcode";
    assert(LOG_FS_OK == Log_IO_Initialize());
    assert(load_or_create_logs());

    assert(!barcode_cast_or_spoiled(barcode, sizeof(barcode)));
    assert(!barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));

    bool logged = log_app_event( APP_EVENT_BALLOT_USER_CAST,
                                 barcode,
                                 sizeof(barcode) );
    assert(logged);
    assert(barcode_cast_or_spoiled(barcode, sizeof(barcode)));
    assert(!barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));

    logged = log_app_event( APP_EVENT_BALLOT_USER_CAST,
                            another_barcode,
                            sizeof(another_barcode) );
    assert(logged);
    assert(barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));
    assert(barcode_cast_or_spoiled(barcode, sizeof(barcode)));

    Log_IO_Close(&app_log_handle);
    Log_IO_Close(&system_log_handle);
    load_or_create_logs();
    assert(barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));
    assert(barcode_cast_or_spoiled(barcode, sizeof(barcode)));
}
