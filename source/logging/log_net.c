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
	size_t length = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;

    char *log_file_name = file_name;

    size_t HEADER_SIZE = 134 + strlen(log_file_name);

    char header[HEADER_SIZE];

    char* HEADER_1 = "POST /";
    char* HEADER_2 = log_file_name;
    char* HEADER_3 = " HTTP/1.1\r\n";
    char* HEADER_4 = "Host: 10.6.6.253\r\n";
    char* HEADER_5 = "User-Agent: sbb/2019\r\n";
    char* HEADER_6 = "Accept: */*\r\n";
    char* HEADER_7 = "Content-Type: application/octet-stream\r\n";
    char* HEADER_8 = "Content-Length: ";
    size_t HEADER_9 = length;
    char* HEADER_10="\r\n\r\n";
    snprintf(header, HEADER_SIZE, "%s%s%s%s%s%s%s%s%zu%s",
             HEADER_1, HEADER_2, HEADER_3, HEADER_4,
             HEADER_5, HEADER_6, HEADER_7, HEADER_8,
             HEADER_9, HEADER_10);
	return;
}

#endif

