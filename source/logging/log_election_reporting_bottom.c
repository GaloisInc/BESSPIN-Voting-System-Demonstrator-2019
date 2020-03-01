#include "votingdefs.h"
#include "logging/log_election_reporting_t.h"
#include "logging/log_election_reporting.h"

ER_STATUS Election_Report_Endpoint_Name(endpoint_name_t resource_name,
                                        endpoint_name_t endpoint_name,
                                        size_t          endpoint_max_size)
{
    (void)resource_name;
    (void)endpoint_name;
    (void)endpoint_max_size;
    osd_assert(0);
    return ER_ERR;
}

ER_STATUS Election_Report_Application_Entry(endpoint_name_t   endpoint,
                                            election_report_t report,
                                            size_t            report_size)
{
    (void)endpoint;
    (void)report;
    (void)report_size;
    osd_assert(0);
    return ER_ERR;
}
