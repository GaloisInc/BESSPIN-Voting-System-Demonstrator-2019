#!/bin/bash
CONTAINER_NAME=besspin_voting_system_public
IMAGE_NAME=galoisinc/besspin
IMAGE_TAG=besspin_base_image

# Linux and OS X ?
unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     SUDO=sudo;;
    Darwin*)    SUDO=;;
    *)          echo "Unknown machine. "; exit 1;;
esac

# Assume we are running from voting-system/docker directory
TOOL_SUITE_PATH=`pwd`/../tool-suite/

if [[ -z "${SOURCE_MOUNT_SSH_POINT}" ]]; then
  echo "SOURCE_MOUNT_SSH_POINT is undefined. Provide keys for docker build."
  echo "Exiting..."
  exit 1
fi

echo "TOOL_SUITE_PATH=$TOOL_SUITE_PATH"
echo "SOURCE_MOUNT_SSH_POINT=$SOURCE_MOUNT_SSH_POINT"

DATETIME=$(date +"%Y-%m-%d %T")

if [[ $1 == "--erase" ]]; then
	erase_images=true
else
	erase_images=false
fi

echo [$DATETIME] Start building BESSPIN Voting System Image.

if [ "$erase_images" = true ];
then

echo [$DATETIME] Remove all containers locally.
$SUDO docker rm -f $($SUDO docker ps -a -q)
if [[ $? -ne 0 ]]
then
  echo "Error: Remove all containers locally."
fi

echo [$DATETIME] Remove all images locally.
$SUDO docker rmi $($SUDO docker images -a -q)
if [[ $? -ne 0 ]]
then
  echo "Error: Remove all images locally."
fi

fi # if [ "$erase_images" = true ];

echo [$DATETIME] Create image locally.
$SUDO docker build -t "master_image" .
if [[ $? -ne 0 ]]
then
  echo "Error: Create image locally."
  exit 1
fi

echo [$DATETIME] Create container $CONTAINER_NAME.
$SUDO docker run -t -d -P -v $SOURCE_MOUNT_SSH_POINT:/root/.ssh -v $TOOL_SUITE_PATH:/tool-suite --name=$CONTAINER_NAME  --privileged master_image
if [[ $? -ne 0 ]]
then
  echo "Error: Create container $CONTAINER_NAME."
  exit 1
fi

echo "[$DATETIME] nix-shell installation in progress."
$SUDO docker exec -u 0 $CONTAINER_NAME /bin/sh -c "ssh-keyscan gitlab-ext.galois.com >> /root/.ssh/known_hosts"
$SUDO docker exec -u 0 $CONTAINER_NAME /bin/sh -c "nix-shell /tool-suite/nix/dev/voting-system-public.nix --show-trace"
if [[ $? -ne 0 ]]
then
  echo "Error: nix-shell installation"
  exit 1
fi

echo [$DATETIME] Commit and tag docker container.
$SUDO docker commit $($SUDO docker ps -aqf "name=$CONTAINER_NAME") $IMAGE_NAME:$IMAGE_TAG
if [[ $? -ne 0 ]]
then
  echo "Error: Commit and tag docker container."
  exit 1
fi

if [ "$erase_images" = true ];
then

echo [$DATETIME] Remove force $CONTAINER_NAME.
$SUDO docker rm -f $CONTAINER_NAME
if [[ $? -ne 0 ]]
then
  echo "Error: Remove force $CONTAINER_NAME."
  exit 1
fi

echo [$DATETIME] Remove master latest image.
$SUDO docker image rm master_image
if [[ $? -ne 0 ]]
then
  echo "Error: Remove master latest image."
  exit 1
fi

fi # if [ "$erase_images" = true ];

# TODO: make sure you are logged into docker hub: $SUDO docker login --username=...
echo [$DATETIME] Publish the image.
$SUDO docker push galoisinc/besspin:besspin_base_image
if [[ $? -ne 0 ]]
then
  echo "Error: Publish the image."
  exit 1
fi

echo [$DATETIME] Docker BESSPIN Voting System container installed successfully.


