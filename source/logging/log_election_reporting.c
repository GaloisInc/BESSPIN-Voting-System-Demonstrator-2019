#include "votingdefs.h"
#include "logging/log_net.h"
#include "logging/log_election_reporting_t.h"
#include "logging/log_election_reporting.h"

#define TOPLEVEL_ENDPOINT_PREFIX "elections/"

ER_STATUS Election_Report_Endpoint_Name(election_name_t election_name,
                                        endpoint_t      endpoint_name,
                                        size_t          endpoint_max_size)
{
    ER_STATUS succeed = ER_ERR;

    const size_t prefix_size   = strlen(TOPLEVEL_ENDPOINT_PREFIX);
    const size_t election_size = strlen(election_name);

    if ( prefix_size + election_size <= endpoint_max_size ) {
        strncpy(endpoint_name, TOPLEVEL_ENDPOINT_PREFIX, prefix_size);
        strncat(endpoint_name, election_name, endpoint_max_size - prefix_size);
        succeed = ER_OK;
    }

    return succeed;
}

ER_STATUS Election_Report_Application_Entry(endpoint_t        endpoint,
                                            election_report_t report,
                                            size_t            report_size)
{
    Log_Net_Send(endpoint, report, report_size);
    return ER_OK;
}
