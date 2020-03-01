# BESSPIN Voting System Docker Images

Docker is used to provide a standard development environment for the
BESSPIN Voting System.  The Docker images here depend upon other
project Docker images, such as the SSITH GFE Docker image.

# Docker Tutorial

Docker is an open-source project that automates the deployment of
software applications inside containers by providing an additional
layer of abstraction and automation of OS-level virtualization on
Linux. This document provides basic Docker commands.
For more information please see the 
[Docker overview](<https://docs.docker.com/engine/docker-overview/> "Docker overview") 
official site.

## Docker Concepts

1. `Docker images` are read-only binary templates that serve for
   creating containers.

2. `Containers` are instances of images that are created by combining
   the `base` image and the layers on top of it.

3. `Registries` are holders for Docker images. Public registry is
   called `Docker Hub`.

4. 	`Repository` is a collection of images tracked by GUIDs. Different
	version of an image can be managed by multiple tags, saved with
	different GUIDs.

# Docker Commands

For finding help with Docker commands on Linux-based systems, you can
use the `man` command.  Here are some examples.

- `man docker`
- `man docker ps`
- `man docker exec`

## Docker Daemon Commands

The default Docker daemon configuration file is located (in Linux) at
`/etc/sysconfig/docker`, which is used while starting the daemon.
Here are some basic operations:

- enable service: `systemctl enable docker`
- start daeamon: `systemctl start docker`
- stop daeamon: `systemctl stop docker`
- restart daeamon: `systemctl restart docker`
- Docker info: `docker info` 
- version : `docker version`

For macOS:

- restart deamon: `killall Docker && open /Applications/Docker.app`

## Docker Images

- find image: `docker search CONDITION`

  example: `docker search ubuntu |  head -n3`

- find popular images  - stars filter option

  example: `docker search --filter=stars=300 --automated ubuntu` 

- Image tags group images of the same type - pull tagged image:
  `docker pull NAME[:TAG]`

  example: `docker pull galoisinc/besspin:voting_system`

- list images of local registry available on the system: `docker
  images`

  example:

  ```
  $ docker images
  REPOSITORY          TAG                  IMAGE ID            CREATED             SIZE
  galoisinc/besspin   voting_system   48a07c86a2a4        2 days ago          12.5GB 
  ```

- remove image: `docker rmi IMAGE[:TAG]`

  example pull then remove: 
  ```
  $ docker pull darksheer/ubuntu; docker rmi darksheer/ubuntu
  ```

## Docker Containers

- list containers

  example:
  ```
  $ docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS              PORTS               NAMES
  1cb9cb9718b2        galoisinc/besspin:voting_system   "/bin/bash"         3 hours ago         Up 3 hours                              besspin_base
  ```

 - stop container 

   example:

   ```
   $ docker stop besspin_base; docker ps -a
   besspin_base
   CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                      PORTS               NAMES
   1cb9cb9718b2        galoisinc/besspin:voting_system   "/bin/bash"         3 hours ago         Exited (0) 50 seconds ago                       besspin_base
   ```
 - start container

   example:

   ```
   $ docker start besspin_base; docker ps -a
   besspin_base
   CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                  PORTS               NAMES
   07ddbd3afc1a        galoisinc/besspin:voting_system   "/bin/bash"         About an hour ago   Up Less than a second                       besspin_base
   ```

 - remove container

   ```
   $ docker rm besspin_base; docker ps -a
   besspin_base
   CONTAINER ID        IMAGE               COMMAND             CREATED             STATUS              PORTS               NAMES
   ```

- run container: `docker run [ OPTIONS ]  IMAGE[:TAG]  [COMMAND]  [ARG...]`

  example: run in an iterative mode without detaching:
  ```
  $ docker run -it -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:voting_system
  root@besspin_base:/tool-suite# 
  ```
  If you type the `exit` command, container will be stopped. 
  (see above how to start container)
  ```
  $ docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                     PORTS               NAMES
  c8cfa0b56cae        galoisinc/besspin:voting_system   "/bin/bash"         11 minutes ago      Exited (0) 3 seconds ago                       besspin_base
  ``` 

  example: run detached container - start in the background mode:

  ```
  $ docker run -t -d -P -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:voting_system
  be995b4b4baa7aaeb54409470ae93f28c22581ac0152d4acc205611b24fadfc1

  $docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS              PORTS               NAMES
  be995b4b4baa        galoisinc/besspin:voting_system   "/bin/bash"         2 minutes ago       Up 2 minutes                            besspin_base

  $ docker exec -it besspin_base /bin/bash
   root@besspin_base:/tool-suite# 
  ```

  If you type the `exit` command, container will stay in `active` mode.
  
  ```
  $ docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS              PORTS               NAMES
  be995b4b4baa        galoisinc/besspin:voting_system   "/bin/bash"         6 minutes ago       Up 6 minutes                            besspin_base 
  ```
  It should be noted that starting container in the background mode 
  returns `container ID`. Therefore, we can attach container latter on.

  ```
  $ ID=$(docker run -t -d -P -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:voting_system)

  $ docker attach $ID
  root@besspin_base:/tool-suite# 
  ``` 

- remove-force Docker container:

  example: 

  `docker rm -f besspin_base`

- execute command outside of the Docker container

  example:

  ```
  $ docker exec -u 0 besspin_base /bin/bash -c "cat /etc/hosts"
  127.0.0.1	localhost
  ::1	localhost ip6-localhost ip6-loopback
  fe00::0	ip6-localnet
  ff00::0	ip6-mcastprefix
  ff02::1	ip6-allnodes
  ff02::2	ip6-allrouters
  172.17.0.2	besspin_base
  ```

 - inspect container `docker inspect [-f|--format="" CONTAINER|IMAGE [CONTAINER|IMAGE]`

   example:

   ```
   $ docker inspect besspin_base
   $
   $ defaultIP=$(docker inspect -f '{{.NetworkSettings.IPAddress}}' besspin_base )
   $ echo $defaultIP
   172.17.0.2
   ``` 

 - commit container - `docker commit -a|--author[=""] -m|--message[=""] CONTAINER [REPOSITORY[:TAG]]`

   example:
   ```
   $ docker commit $(docker ps -aqf "name=besspin_base") galoisinc/besspin:voting_system1
     sha256:6659255be4c2bdd3b00b02067d0b7b598b6b50aadb42e9550934cdbda254ca16
   $ docker images
   REPOSITORY          TAG                   IMAGE ID            CREATED             SIZE
   galoisinc/besspin   voting_system1   6659255be4c2        4 seconds ago       12.5GB
   galoisinc/besspin   besspin_base_image    48a07c86a2a4        2 days ago          12.5GB
   ```
 - save one or more images to a tar archive - locally

   example:

   ```
   $ docker save --output besspin_base.tar besspin_base
   ```

 - load docker image from archive

   example:

   ```
   $ docker load --input besspin_base.tar
   ```

## Frequently Used Docker Commands for Daily Work

```
docker build -t Dockerfile .                        # Create image using this directory's Dockerfile
docker build -f <docker file name> .                # Create image using this directory's <docker file name>
docker container ls                                 # List all running containers
docker container ls -a                              # List all containers, even those not running
docker container stop <hash>                        # Gracefully stop the specified container
docker container kill <hash>                        # Force shutdown of the specified container
docker container rm <hash>                          # Remove specified container from this machine
docker container rm $(docker container ls -a -q)    # Remove all containers
docker image ls -a                                  # List all images on this machine
docker image rm <image id>                          # Remove specified image from this machine
docker image rm $(docker image ls -a -q)            # Remove all images from this machine
docker login                                        # Log in this CLI session using your Docker credentials
docker tag <image> username/repository:tag          # Tag <image> for upload to registry
docker push username/repository:tag                 # Upload tagged image to registry
docker run username/repository:tag                  # Run image from a registry
```

## Test the galoisinc/besspin:voting_system Docker Image

1.	[Install](<https://docs.docker.com/install/linux/docker-ce/ubuntu/>) 
    Docker on your machine.
2.  `sudo docker pull galoisinc/besspin:voting_system`
3.  Make sure you have the docker branch of the voting system repo.
4.  Make sure you have the right image downloaded:

    ```
    $ docker images
	  REPOSITORY          TAG                  IMAGE ID            CREATED             SIZE
	  galoisinc/besspin   voting_system   48a07c86a2a4        3 days ago          12.5GB
    ```

5. Run it using `IMAGE_ID` or `REPOSITORY:TAG` and instead of
   `$PATH_TO_YOUR_VOTING_SYSTEM_REPO` put the absolute path to your
   voting system repo:

    ```
    sudo docker run  --name="besspin_base" --hostname="besspin_base" -v $PATH_TO_YOUR_VOTING_SYSTEM_REPO:/voting-system -it galoisinc/besspin:voting_system
    ```
    
6. In Docker do:

    ```
    # cd /voting-system
    # make fpga
    ```

7. If everything went well, you will see FreeRTOS FPGA target
   building.

8. Type `exit` to get out of the container

## Development with Docker

### Code compilation

A good development workflow is following:

1. Open the `voting-system` code in your editor of choice.

2. In new terminal, run the Docker container interactively. 
 
```
sudo docker run -v $PATH_TO_YOUR_VOTING_SYSTEM_REPO:/voting-system -it galoisinc/besspin:voting_system
```
    Compile / verify the code from within the container.

3. In another terminal, you can access `voting-system` repo you shared
   with the Docker container.  So, for example, changes in source code
   can be committed to GitHub etc. while the Docker container is still
   running.

### Code Deployment and Debugging

We will need one container running the `openocd` server, and a second
container running the `gdb` instance. You also need a properly
connected FPGA, and your host needs to have all the Xilinx drivers
installed as well.

To actually upload and debug the code, you need to run the container
in `priviledged` mode. That way the container has access to the USB
devices on the host. See 
[Docker Documentation](https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities)
for more info.

We also have to connect the container to host network, so we can
communicate between the two containers. Use `--network host` for that.

Note that one cannot use Docker on macOS for FPGA control and
debugging unless one is willing to [setup a VirtualBox-based Docker
installation](http://gw.tnode.com/docker/docker-machine-with-usb-support-on-windows-macos/),
rather than the native HyperKit hypervisor.

Now, the actual instructions.

1. Start up `galoisinc/besspin:gfe` container that will run `openocd` 
   server. Note, you will need access to the 
   [gfe](https://gitlab-ext.galois.com/ssith/gfe) repository.  We
   suggest mounting it as follows.
```
sudo docker run --privileged --hostname="gfe" -p 3333:3333 --network host -it -v $PATH_TO_GFE:/gfe galoisinc/besspin:gfe
```

2. Configure and start `openocd`.
    ```
    root@gfe:/gfe# openocd -f testing/targets/ssith_gfe.cfg
    ```
    You will see output like this:
    ```
    root@gfe:/gfe# openocd -f testing/targets/ssith_gfe.cfg 
    Open On-Chip Debugger 0.10.0+dev-00617-g27c0fd7a7 (2019-09-24-00:09)
    Licensed under GNU GPL v2
    For bug reports, read
      http://openocd.org/doc/doxygen/bugs.html
    adapter speed: 2000 kHz
    ftdi samples TDO on falling edge of TCK
    none separate
    Info : clock speed 2000 kHz
    Info : JTAG tap: riscv.cpu tap/device found: 0x14b31093 (mfg: 0x049 (Xilinx), part: 0x4b31, ver: 0x1)
    Info : datacount=1 progbufsize=16
    Info : Disabling abstract command reads from CSRs.
    Info : Examined RISC-V core; found 1 harts
    Info :  hart 0: XLEN=32, misa=0x40001105
    Info : Listening on port 3333 for gdb connections
    Info : JTAG tap: riscv.cpu tap/device found: 0x14b31093 (mfg: 0x049 (Xilinx), part: 0x4b31, ver: 0x1)
    Info : Listening on port 6666 for tcl connections
    Info : Listening on port 4444 for telnet connections
    Info : accepting 'gdb' connection on tcp/3333
    Info : dropped 'gdb' connection
    Info : accepting 'gdb' connection on tcp/3333
    Info : Hart 0 unexpectedly reset!
    Info : dropped 'gdb' connection
    Info : accepting 'gdb' connection on tcp/3333
    Info : Disabling abstract command writes to CSRs.
```

3. Start `galoisinc/besspin:voting_system` container: 
```
sudo docker run --privileged --hostname="voting-system" --network host -it -v $PATH_TO_VOTING_SYSTEM_REPO:/voting-system galoisinc/besspin:voting_system 
``` 
Compile your code and start `gdb`: 
```
# make clean_all all
# 
# riscv64-unknown-elf-gdb -x startup.gdb default_ballot_box.elf 
``` 
You should see: 
```
    # riscv64-unknown-elf-gdb -x startup.gdb
    default_ballot_box.elf GNU gdb (GDB) 8.3.0.20190516-git
    Copyright (C) 2019 Free Software Foundation, Inc.  License GPLv3+:
    GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html> This
    is free software: you are free to change and redistribute it.
    There is NO WARRANTY, to the extent permitted by law.  Type "show
    copying" and "show warranty" for details.  This GDB was configured
    as "--host=x86_64-pc-linux-gnu --target=riscv64-unknown-elf".
    Type "show configuration" for configuration details.  For bug
    reporting instructions, please see:
    <http://www.gnu.org/software/gdb/bugs/>.  Find the GDB manual and
    other documentation resources online at:
    <http://www.gnu.org/software/gdb/documentation/>.

    For help, type "help".
    Type "apropos word" to search for commands related to "word"...
    Reading symbols from default_ballot_box.elf...
    boot () at ../FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1/bsp/boot.S:76
    76	    li t6, 0x1800
    $1 = "Reseting the CPU"
    0x44000000 in ?? ()
    $2 = "Loading binary"
    Loading section .text, size 0x68004 lma 0xc0000000
    Loading section .rodata, size 0x78f0 lma 0xc0080000
    Loading section .eh_frame, size 0x3c lma 0xc00878f0
    Loading section .sdata, size 0x228 lma 0xc0087978
    Loading section .data, size 0xfe4 lma 0xc0087ba0
    Start address 0xc0000000, load size 461628
    Transfer rate: 103 KB/sec, 13988 bytes/write.
    (gdb) 
```

4. Start debugging! 
