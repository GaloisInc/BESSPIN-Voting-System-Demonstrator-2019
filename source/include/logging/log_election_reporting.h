/**
 * Smart Ballot Logging Election Reporting
 * @refine log.lando
 */
#include "logging/log_t.h"

// Election_Report_System_Entry      : Stream -> Entry -> ()
typedef enum { ER_OK, ER_ERR } ER_STATUS;

// Build the endpoint name
endpoint_t Election_Report_Endpoint_Name(election_name_t election_name);

// Send a log_entry as a report
ER_STATUS  Election_Report_System_Entry(endpoint_t endpoint, election_report_t report);
