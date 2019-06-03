#include <logging.h>

bool is_the_same_hash_code(LogEntry *le1, LogEntry *le2) {
    return (le1 -> hash == le2 -> hash)? true : false;
}

int save_entry_to_log(LogEntry *le, char * _logname, char * _mode) {
    FILE * _log = fopen (_logname,_mode);
    //@ ghost g_log = _log;
    if (_log == NULL)
    {
        return _FILE_ERROR;
    }
    fwrite (le, sizeof(LogEntry), 1, _log);
    if(&fwrite == 0) 
    {
        return _IO_ERROR;
    }
    fclose (_log);
    return _SUCCESS;
}

