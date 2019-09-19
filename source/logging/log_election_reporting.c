#include "votingdefs.h"
#include "logging/log_net.h"
#include "logging/log_election_reporting_t.h"
#include "logging/log_election_reporting.h"
#include <stdio.h>

#define TOPLEVEL_ENDPOINT_PREFIX "elections"

ER_STATUS Election_Report_Endpoint_Name(endpoint_name_t resource_name,
                                        endpoint_name_t endpoint_name,
                                        size_t          endpoint_max_size)
{
    ER_STATUS succeed = ER_ERR;

    const size_t prefix_size   = strlen(TOPLEVEL_ENDPOINT_PREFIX);
    const size_t resource_size = strlen(resource_name);

    if ( prefix_size + resource_size <= endpoint_max_size ) {
        int write = snprintf(endpoint_name,
                             endpoint_max_size,
                             "%s/%s",
                             TOPLEVEL_ENDPOINT_PREFIX,
                             resource_name);
        succeed = (write > 0) ? ER_OK : ER_ERR;
    }

    return succeed;
}

ER_STATUS Election_Report_Application_Entry(endpoint_name_t   endpoint,
                                            election_report_t report,
                                            size_t            report_size)
{
    Log_Net_Send(endpoint, report, report_size);
    return ER_OK;
}
