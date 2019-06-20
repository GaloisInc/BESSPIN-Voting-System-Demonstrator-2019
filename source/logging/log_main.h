// Implementation of all Logging subsystem scenarios.

#include "log.h"

void Empty_Log_Smoketest(const log_name the_log_name,
                         const log_io_stream a_target);
void Import_Export_Empty_Log(const log_name the_log_name,
                             const log_io_stream a_target);
void Non_Empty_Log_Smoketest(const log_name the_log_name,
                             const log_io_stream a_target);
void Import_Export_Non_Empty_Log(const log_name the_log_name,
                                 const log_io_stream a_target);
