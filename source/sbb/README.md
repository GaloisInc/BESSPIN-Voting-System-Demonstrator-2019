# Smart Ballot Box
How to understand this repository?

* The header and source files are the refinement of `sbb.lando`
* To compile **bottom** implementation: `TARGET=bottom make`
* To compile **FreeRTOS** implementation: `TARGET=freertos make`
* To run **verification**: `TARGET=verification make`
* In each case, you can run `make clean` to remove the generated artifacts