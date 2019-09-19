/**
 * Smart Ballot Logging Election Reporting
 */
#include "logging/log_t.h"
#include "logging/log_election_reporting_t.h"

typedef enum { ER_OK, ER_ERR } ER_STATUS;

/*@ requires valid_read_string(resource_name);
  @ requires \valid(endpoint_name + (0 .. endpoint_max_size - 1));
  // @ assigns *(endpoint_name + (0 .. endpoint_max_size - 1));
*/
ER_STATUS Election_Report_Endpoint_Name(endpoint_name_t resource_name,     //IN
                                        endpoint_name_t endpoint_name,     //OUT
                                        size_t          endpoint_max_size);//IN

/*@ requires valid_read_string(endpoint);
  @ requires \valid_read(report + (0 .. report_size - 1));
*/
ER_STATUS Election_Report_Application_Entry(endpoint_name_t   endpoint,    //IN
                                            election_report_t report,      //IN
                                            size_t            report_size);//IN
