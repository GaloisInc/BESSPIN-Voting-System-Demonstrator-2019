# Docker Tutorial
Docker is an open-source project that automates the deployment of software applications 
inside containers by providing an additional layer of abstraction and automation of OS-level 
virtualization on Linux. This document provides basic docker commands.
For more information please see the [Docker overview](<https://docs.docker.com/engine/docker-overview/> "Docker overview") official site.  

## Docker keywords:

1. `Docker images` are read-only binary templates that serve for creating containers.

2. `Containers`  are instances of images that are created by combining the `base` image and the layers on top of it.

3. `Registries` are holders for Docker images. Public registry is called `Docker Hub`.

4. 	`Repository` is a collection of images tracked by GUIDs. Different version of an image can be managed by multiple tags, saved 
	with different GUIDs.


# Docker commands:

For finding help with docker commands on Linux-based systems, you can use the `man` command.
Here are some examples.

- `man docker`

- `man docker ps`

- `man docker exec`

## Docker daemon commands for Linux:

The default Docker daemon configuration file is located at `/etc/sysconfig/docker`, which is used while starting the daemon. 
Here are some basic operations:

- enable service: `systemctl enable docker`

- start daeamon: `systemctl start docker`

- stop daeamon: `systemctl stop docker`

- restart daeamon: `systemctl restart docker`

- docker info: `docker info` 

- version : `docker version`

For macOS:

- restart deamon: `killall Docker && open /Applications/Docker.app`

## Docker Images

- find image: `docker search CONDITION`

  example: `docker search ubuntu |  head -n3`

- find popular images  - stars filter option

  example: `docker search --filter=stars=300 --automated ubuntu` 

- Image tags group images of the same type - pull tagged image: `docker pull NAME[:TAG]`

  example: `docker pull galoisinc/besspin:besspin_base_image`

- list images of local registry available on the system: `docker images`

  example:

  ```
  $ docker images
  REPOSITORY          TAG                  IMAGE ID            CREATED             SIZE
  galoisinc/besspin   besspin_base_image   48a07c86a2a4        2 days ago          12.5GB 
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
  1cb9cb9718b2        galoisinc/besspin:besspin_base_image   "/bin/bash"         3 hours ago         Up 3 hours                              besspin_base
  ```

 - stop container 

   example:

   ```
   $ docker stop besspin_base; docker ps -a
   besspin_base
   CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                      PORTS               NAMES
   1cb9cb9718b2        galoisinc/besspin:besspin_base_image   "/bin/bash"         3 hours ago         Exited (0) 50 seconds ago                       besspin_base
   ```
 - start container

   example:

   ```
   $ docker start besspin_base; docker ps -a
   besspin_base
   CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                  PORTS               NAMES
   07ddbd3afc1a        galoisinc/besspin:besspin_base_image   "/bin/bash"         About an hour ago   Up Less than a second                       besspin_base
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
  $ docker run -it -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:besspin_base_image
  root@besspin_base:/tool-suite# 
  ```
  If you type the `exit` command, container will be stopped. (see above how to start container)
  ```
  $ docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS                     PORTS               NAMES
  c8cfa0b56cae        galoisinc/besspin:besspin_base_image   "/bin/bash"         11 minutes ago      Exited (0) 3 seconds ago                       besspin_base
  ``` 

  example: run detached container - start in the background mode:

  ```
  $ docker run -t -d -P -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:besspin_base_image
  be995b4b4baa7aaeb54409470ae93f28c22581ac0152d4acc205611b24fadfc1

  $docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS              PORTS               NAMES
  be995b4b4baa        galoisinc/besspin:besspin_base_image   "/bin/bash"         2 minutes ago       Up 2 minutes                            besspin_base

  $ docker exec -it besspin_base /bin/bash
   root@besspin_base:/tool-suite# 
  ```

  If you type the `exit` command, container will stay in `active` mode.
  
  ```
  $ docker ps -a
  CONTAINER ID        IMAGE                                  COMMAND             CREATED             STATUS              PORTS               NAMES
  be995b4b4baa        galoisinc/besspin:besspin_base_image   "/bin/bash"         6 minutes ago       Up 6 minutes                            besspin_base 
  ```
  It should be noted that starting container in the background mode returns `container ID`. Therefore, we can attach container latter on.

  ```
  $ ID=$(docker run -t -d -P -v <abs path to>/voting-system:/voting-system  --name="besspin_base" --hostname="besspin_base" galoisinc/besspin:besspin_base_image)

  $ docker attach $ID
  root@besspin_base:/tool-suite# 
  ``` 


- remove-force docker container:

  example: 

  `docker rm -f besspin_base`

- execute command outside of the docker container

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
   $ docker commit $(docker ps -aqf "name=besspin_base") galoisinc/besspin:besspin_base_image1
     sha256:6659255be4c2bdd3b00b02067d0b7b598b6b50aadb42e9550934cdbda254ca16
   $ docker images
   REPOSITORY          TAG                   IMAGE ID            CREATED             SIZE
   galoisinc/besspin   besspin_base_image1   6659255be4c2        4 seconds ago       12.5GB
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

## List of frequently used Docker commands for daily work
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

## Test the galoisinc/besspin:besspin_base_image

1.	[Install](<https://docs.docker.com/install/linux/docker-ce/ubuntu/>) docker on your machine.
2.  `sudo docker pull galoisinc/besspin:besspin_base_image`
3.  Make sure you have the docker branch of the voting system repo.
4.  Make sure you have the right image downloaded:

    ```
    $ docker images
	  REPOSITORY          TAG                  IMAGE ID            CREATED             SIZE
	  galoisinc/besspin   besspin_base_image   48a07c86a2a4        3 days ago          12.5GB
    ```

5. Run it using `IMAGE_ID` or `REPOSITORY:TAG` and instead of `$PATH_TO_YOUR_VOTING_SYSTEM_REPO` put the absolute path to your voting system repo:

    ```
    sudo docker run  --name="besspin_base" --hostname="besspin_base" -v $PATH_TO_YOUR_VOTING_SYSTEM_REPO:/voting-system -it galoisinc/besspin:besspin_base_image
    ```
    
6. In docker do:

    ```
    #cd /voting-system
    #nix-shell
    #make fpga
    ```
7. If everything went well, you will see FreeRTOS FPGA target building.

8. Type `exit` to get out of nix-shell and the container













