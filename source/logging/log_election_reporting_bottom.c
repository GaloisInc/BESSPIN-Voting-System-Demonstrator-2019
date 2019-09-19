#include "votingdefs.h"
#include "logging/log_election_reporting_t.h"
#include "logging/log_election_reporting.h"

ER_STATUS Election_Report_Endpoint_Name(election_name_t election_name,     //IN
                                        endpoint_t      endpoint_name,     //OUT
                                        size_t          endpoint_max_size) //IN
{
    (void)election_name;
    (void)endpoint_name;
    (void)endpoint_max_size;
    osd_assert(0);
    return ER_ERR;
}

ER_STATUS Election_Report_Application_Entry(endpoint_t        endpoint,    //IN
                                            election_report_t report,      //IN
                                            size_t            report_size) //IN
{
    (void)endpoint;
    (void)report;
    (void)report_size;
    osd_assert(0);
    return ER_ERR;
}
