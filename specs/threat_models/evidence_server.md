# Evidence Server Threat Model

## Security Objectives

* Evidence integrity
* Election Key confidentiality & integrity (is the key stored on the ES?)

Notes:

- In pre-election, data flows _from_ most subsystems _to_ the election server (via logs delivered
  by network or SD card).
- In post-election, data mostly flows _from_ election server.
  
Questions:

- When are spoiled ballots decrypted (before or after being stored on evidence server)?

## Threats

- Find crypto keys on disk or in memory
- Learn keys by analyzing network traffic

### During Election 

- Loading server with forged evidence via
    - SD card
        - Election official (i.e. party with correct credentials).
        - Malicious third party with ability to compromise authentication &
          authorization on physical server
    - Network
        - By spoofing identity of BSD or Tabulation device
        - Tampering with dataflow over network

### Post-Election

- Loading server with forged evidence via
    - SD card
        - Election official (i.e. party with correct credentials).
        - Malicious third party with ability to compromise authentication &
          authorization on physical server
    - Network
        - By spoofing identity of BSD or Tabulation device
        - Tampering with dataflow over network
- Alter/delete/add evidence 
    - via malformed API requests
    - via malformed/forged evidence (from BSD or malicious party)
- Arbitrary code execution 
    - via malformed API requests
    - via malformed/forged evidence (from BSD or malicious party)
- Privilege escalation
    - via malformed API requests
    - via malformed/forged evidence (from BSD or malicious party)
- Attacker spoofs election server identity to distribute forged evidence.
- Denial of Service
    - Flood of requests to server for evidence.
