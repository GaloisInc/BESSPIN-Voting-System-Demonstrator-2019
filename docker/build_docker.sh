#!/bin/bash
CONTAINER_NAME=besspin_voting_system
IMAGE_NAME=free_and_fair/besspin
IMAGE_TAG=voting_system

# Linux and OS X ?
unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     SUDO=sudo;;
    Darwin*)    SUDO=;;
    *)          echo "Unknown machine. "; exit 1;;
esac

DATETIME=$(date +"%Y-%m-%d %T")

if [[ $1 == "--erase" ]]; then
	erase_images=true
else
	erase_images=false
fi

echo [$DATETIME] Start building BESSPIN Voting System image.

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

echo [$DATETIME] Tag image.
$SUDO docker tag master_image $IMAGE_NAME:$IMAGE_TAG
if [[ $? -ne 0 ]]
then
  echo "Error: Tag image."
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
$SUDO docker push $IMAGE_NAME:$IMAGE_TAG
if [[ $? -ne 0 ]]
then
  echo "Error: Publish the image."
  exit 1
fi

echo [$DATETIME] Docker BESSPIN Voting System container installed successfully.


