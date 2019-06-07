# Smart Ballot Box
How to understand this repository?

* `cd smart_ballot_box` will get you to the directory with the implementation of [sbb.lando](https://gitlab-ext.galois.com/ssith/voting-system/blob/master/specs/lando/sbb.lando) Here you can call `make bottom` to compile the bottom implementation of smart ballot box, and then `make bottom_clean` to clean it. The makefile also contains verification targets (untested)
* `cd full_demo` will get you to the demo directory (just a parent of `smart_ballot_box`). It contains FreeRTOS as well, so you can build the whole application. How?
    1. in your local copy of [gfe](https://gitlab-ext.galois.com/ssith/gfe) (**NOTE** you must use `develop` branch), type `nix-shell tool-suite/nix/dev/gfe.nix`
    2. cd to the `full_demo` directory
    3. `make` to build the whole app
* To upload/run your code, follow the instructions in the [gfe](https://gitlab-ext.galois.com/ssith/gfe) repository (**NOTE** use `develop` branch)