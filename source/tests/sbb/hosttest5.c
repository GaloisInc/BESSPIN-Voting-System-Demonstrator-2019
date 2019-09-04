#include <assert.h>
#include "logging/log.h"
#include "logging/log_io.h"
#include "sbb/sbb_logging.h"

const log_name system_log_file_name = "sbb_test_system.log";
const log_name app_log_file_name = "sbb_test_app.log";

int main(int argc, char **argv) {
    char barcode[] = "A Barcode";
    char another_barcode[] = "Another Barcode";

    assert(LOG_FS_OK == Log_IO_Initialize());
    assert(LOG_FS_OK == create_log(&app_log_handle, app_log_file_name, HTTP_Endpoint_None));
    Log_IO_Close(&app_log_handle);
    Log_IO_Open(&app_log_handle, app_log_file_name, HTTP_Endpoint_None);
    assert(import_and_verify(&app_log_handle));
    assert(!barcode_cast_or_spoiled(barcode, sizeof(barcode)));
    assert(!barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));

    bool logged = log_app_event( APP_EVENT_BALLOT_USER_CAST,
                                 barcode,
                                 sizeof(barcode) );
    if ( logged ) {
        assert(barcode_cast_or_spoiled(barcode, sizeof(barcode)));
        assert(!barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));
        logged = log_app_event( APP_EVENT_BALLOT_USER_CAST,
                                another_barcode,
                                sizeof(another_barcode) );
        if ( logged ) {
            assert(barcode_cast_or_spoiled(another_barcode, sizeof(another_barcode)));
            assert(barcode_cast_or_spoiled(barcode, sizeof(barcode)));
        }
    }
}
