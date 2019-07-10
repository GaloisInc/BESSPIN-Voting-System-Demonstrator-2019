#include "log_net.h"
#include "debug_io.h"

static const char space = ' ';
static const char new_line = '\n';

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
	
	size_t len = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;
    size_t FIXED_MESSAGE_SIZE = 134;
    char *log_file_name = file_name;
    size_t REQUEST_LINE_HEADER = FIXED_MESSAGE_SIZE + strlen(log_file_name);
    size_t MESSAGE_SIZE = REQUEST_LINE_HEADER + len;
    char message[MESSAGE_SIZE];

    int sockfd, bytes, sent, total;
    char *host = "localhost";
    struct hostent *server;
    struct sockaddr_in serv_addr;
    int PORT_NUMBER = 8066;

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

    
    // add base64_secure_log_entry to the message
    memcpy(&message[REQUEST_LINE_HEADER - 1], &secure_log_entry.the_entry[0], LOG_ENTRY_LENGTH);
    strncat(message, &space,1);
    memcpy(&message[REQUEST_LINE_HEADER + LOG_ENTRY_LENGTH - 1], &secure_log_entry.the_digest[0], 
        SHA256_BASE_64_DIGEST_LENGTH_BYTES + 1);
     strncat(message, &new_line, 1);

    // create socket
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        debug_printf("ERROR opening socket");
    }
    // lookup the ip address
    // notice this is localhost at the moment
    server = gethostbyname(host);
    if (server == NULL) {
        debug_printf("ERROR, no such host");
    }
    memset(&serv_addr,0,sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(PORT_NUMBER);
    memcpy(&serv_addr.sin_addr.s_addr,server->h_addr,server->h_length);

    // connect the socket
    if (connect(sockfd,(struct sockaddr *)&serv_addr,sizeof(serv_addr)) < 0) {
        debug_printf("ERROR connecting the socket");
    }
    total = MESSAGE_SIZE;
    sent = 0;
    do{
        bytes = write(sockfd,message + sent,total - sent);
        if (bytes < 0){
            debug_printf("ERROR writing message to socket");
        }
        if (bytes == 0) {
            break;
        }
        sent += bytes;
    } while (sent < total);
    return;
}

#endif

