# Stage 1: build base image with nix-shell
FROM ubuntu:18.04 AS master-image

RUN apt-get update && apt-get install -y wget git curl

# Enable HTTPS support in wget and set nsswitch.conf to make resolution work within containers
RUN apt-get install -y openssl ca-certificates \
  && echo hosts: dns files > /etc/nsswitch.conf

# Download Nix and install it into the system.
RUN wget https://nixos.org/releases/nix/nix-2.2.1/nix-2.2.1-x86_64-linux.tar.bz2 \
  && echo "e229e28f250cad684c278c9007b07a24eb4ead239280c237ed2245871eca79e0  nix-2.2.1-x86_64-linux.tar.bz2" | sha256sum -c \
  && tar xjf nix-*-x86_64-linux.tar.bz2 \
  && addgroup --gid 30000 nixbld \
  && for i in $(seq 1 30); do adduser --disabled-password --gecos --no-create-home --uid $((30000 + i)) nixbld$i; usermod -a -G nixbld nixbld$i ; done \
  && mkdir -m 0755 /etc/nix \
  && echo 'sandbox = false' > /etc/nix/nix.conf \
  && mkdir -m 0755 /nix && USER=root sh nix-*-x86_64-linux/install \
  && ln -s /nix/var/nix/profiles/default/etc/profile.d/nix.sh /etc/profile.d/ \
  && rm -r /nix-*-x86_64-linux* \
  && rm -rf /var/cache/apk/* \
  && /nix/var/nix/profiles/default/bin/nix-collect-garbage --delete-old \
  && /nix/var/nix/profiles/default/bin/nix-store --optimise \
  && /nix/var/nix/profiles/default/bin/nix-store --verify --check-contents

ENV \
    ENV=/etc/profile \
    USER=root \
    PATH=/nix/var/nix/profiles/default/bin:/nix/var/nix/profiles/default/sbin:/bin:/sbin:/usr/bin:/usr/sbin \
    GIT_SSL_CAINFO=/nix/var/nix/profiles/default/etc/ssl/certs/ca-bundle.crt \
    NIX_PATH=/nix/var/nix/profiles/per-user/root/channels \
    NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt \
    SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt \
    GIT_SSL_CAINFO=/etc/ssl/certs/ca-certificates.crt

# Set the working directory
WORKDIR /tool-suite

# NOTE: just temporary
# Allow building broken packages (needed for cryptol)
RUN mkdir -p /root/.config/nixpkgs/
RUN echo "{ allowBroken = true; }" > /root/.config/nixpkgs/config.nix

# make sure your domain is accepted
RUN mkdir -p /root/.ssh/ && touch /root/.ssh/known_hosts
RUN ssh-keyscan gitlab-ext.galois.com >> /root/.ssh/known_hosts
RUN ssh-keyscan github.com >> /root/.ssh/known_hosts

# Install clang and make
RUN apt-get update && apt-get install -y clang make