#!/usr/bin/env python

"""
    HTTP Server for Receiving Ballot Box Logs
    Written by Daniel M. Zimmerman (dmz@freeandfair.us)
    Copyright (C) 2019 Free & Fair
"""

from http.server import HTTPServer, BaseHTTPRequestHandler
import os

# SYMBOLIC CONSTANTS

PORT_NUMBER = 8066
""" The port number on which the server will listen for log entries. """

class LogRequestHandler(BaseHTTPRequestHandler):
    """ Handle POST requests with log entries. The assumption is that
        an external firewall or other mechanism prevents most malicious
        connections, and only minimal sanity checking is done on requests
        before saving them to files. """

    def do_POST(self):
        content_length = int(self.headers['Content-Length'])
        body = self.rfile.read(content_length)
        if len(body) != content_length:
            self.send_error(500, explain = 'invalid content length')
            return

        # check that the path doesn't contain an OS path separator or / except
        # at character 0
        if self.path[0] is not "/":
            self.send_error(500, explain = 'invalid endpoint, no leading /')
            return
        log_path = self.path[1:]
        if ("/" in log_path) or (os.path.sep in log_path):
            self.send_error(500, explain = 'path separator detected')
            return

        # the path is safe... let's try to write the body there, followed by
        # a CRLF (b'\r\n', in bytes)

        try:
            print('trying to open file ' + log_path)
            with open(log_path, 'ab') as log_file:
                log_file.write(body)
                log_file.write(b'\r\n')
        except:
            self.send_error(500, explain = 'invalid log file name')
            return

        self.send_response(200)
        self.end_headers()

if __name__ == '__main__':
    # parse the command line
    # TBD

    # create our server
    httpd = HTTPServer(('', PORT_NUMBER), LogRequestHandler)
    httpd.serve_forever()
