/**
 * Smart Ballot Logging Election Reporting
 */
#include "logging/log_t.h"
#include "logging/log_election_reporting_t.h"

typedef enum { ER_OK, ER_ERR } ER_STATUS;

// Build the endpoint name
ER_STATUS Election_Report_Endpoint_Name(endpoint_name_t resource_name,     //IN
                                        endpoint_name_t endpoint_name,     //OUT
                                        size_t          endpoint_max_size);//IN

// Send a log_entry as a report
ER_STATUS Election_Report_Application_Entry(endpoint_name_t   endpoint,    //IN
                                            election_report_t report,      //IN
                                            size_t            report_size);//IN
