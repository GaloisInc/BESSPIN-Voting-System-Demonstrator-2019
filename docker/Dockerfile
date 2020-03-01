# Reuse besspin:base
FROM galoisinc/besspin:gfe

# Install needed packages
RUN apt-get update && apt-get install -y wget git curl make opam unzip lsb-release \
    autoconf libgmp3-dev m4 software-properties-common

# Install Cryptol
RUN apt-get install libtinfo5
RUN wget https://github.com/GaloisInc/cryptol/releases/download/2.8.0/cryptol-2.8.0-Ubuntu14.04-64.tar.gz
RUN tar xvzf cryptol-2.8.0-Ubuntu14.04-64.tar.gz
RUN cp -r cryptol-2.8.0-Ubuntu14.04-64/bin/* /usr/local/bin/
RUN cp -r cryptol-2.8.0-Ubuntu14.04-64/share/* /usr/local/share
RUN rm cryptol-2.8.0-Ubuntu14.04-64.tar.gz

# Install Z3 solver
RUN apt-get install -y unzip
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip
RUN unzip z3-4.7.1-x64-ubuntu-16.04.zip
RUN cp -r z3-4.7.1-x64-ubuntu-16.04/bin/* /usr/local/bin/
RUN cp -r z3-4.7.1-x64-ubuntu-16.04/include/* /usr/local/include/
RUN rm z3-4.7.1-x64-ubuntu-16.04.zip

# Set the working directory
WORKDIR /voting-system

# Additional tools
RUN apt-get install -y bash-completion emacs xxd
#         clang-format clang-tidy

# #  Opam
RUN apt-get update
# RUN apt-get install -y opam
# RUN apt-get install -y zlib1g-dev libgmp-dev libgtksourceview2.0-dev libgnomecanvas2-dev autoconf
# RUN apt-get install -y graphviz
# RUN opam init -y --disable-sandboxing --auto-setup
# RUN opam update
# RUN opam install depext -y
# RUN opam depext zarith lablgtk conf-gtksourceview conf-gnomecanvas -y
# RUN opam install -y zarith lablgtk conf-gtksourceview conf-gnomecanvas
# RUN opam install yojson -y
# RUN opam install coq -y
# RUN opam install why why3 -y
# RUN opam config env

# # Frama-C install
RUN mkdir -p /tools
# RUN wget https://github.com/Frama-C/Frama-C-snapshot/wiki/downloads/frama-c-19.0-Potassium.tar.gz -P /tools
# RUN cd /tools && tar -xf frama-c-19.0-Potassium.tar.gz
# RUN rm /tools/frama-c-19.0-Potassium.tar.gz
# RUN opam depext frama-c
# RUN opam install --deps-only frama-c
# RUN opam pin add --kind=path frama-c /tools/frama-c-19.0-Potassium -y

# cmake is used for ElectionGuard builds. The apt version of cmake is
# a bit too old.
# cmake install
RUN apt-get install -y libgmp3-dev
RUN cd /tools && wget https://github.com/Kitware/CMake/releases/download/v3.16.4/cmake-3.16.4.tar.gz && tar -xf cmake-3.16.4.tar.gz && cd cmake-3.16.4
RUN ./bootstrap -- -DCMAKE_USE_OPENSSL=OFF 
RUN make && make install

ENV PATH="/root/.opam/default/bin:/opt/riscv/bin:${PATH}"
