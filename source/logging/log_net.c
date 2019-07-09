#include "log_net.h"
#include "debug_io.h"

#ifdef TARGET_OS_FreeRTOS

void Log_NET_Initialize() {
	debug_printf("FreeRTOS_IPInit\r\n");
	FreeRTOS_IPInit(uIPAddress, uNetMask, uGatewayAddress, uDNSServerAddress, uMACAddress);
}

void Log_NET_Send(base64_secure_log_entry secure_log_entry) {
	return;
}

#else

void Log_NET_Initialize() {
	return;
}

void Log_NET_Send(base64_secure_log_entry secure_log_entry, log_name file_name) {
	// create header
	size_t len = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;
    size_t FIXED_MESSAGE_SIZE = 134;
    char *log_file_name = file_name;

    size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + strlen(log_file_name) + len;

    char message[MESSAGE_SIZE];

    char* REQUEST_LINE_1 = "POST /";
    char* REQUEST_LINE_2 = log_file_name;
    char* REQUEST_LINE_3 = " HTTP/1.1\r\n";
    char* HEADER_1 = "Host: 10.6.6.253\r\n";
    char* HEADER_2 = "User-Agent: sbb/2019\r\n";
    char* HEADER_3 = "Accept: */*\r\n";
    char* HEADER_4 = "Content-Type: application/octet-stream\r\n";
    char* HEADER_5_1 = "Content-Length: ";
    size_t HEADER_5_2 = len;
    char* DOUBLE_CRLF = "\r\n\r\n";
    snprintf(message, MESSAGE_SIZE, "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, REQUEST_LINE_2, REQUEST_LINE_3, HEADER_1,
             HEADER_2, HEADER_3, HEADER_4, HEADER_5_1,
             HEADER_5_2, DOUBLE_CRLF);
	return;
}

#endif

