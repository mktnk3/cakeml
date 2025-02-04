This directory contains scripts that compile the CakeML compiler
inside the logic to produce the verified machine code version of the
64-bit compiler.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[proofs](proofs):
This directory contains the end-to-end correctness theorem for the
64-bit version of the CakeML compiler.

[repl_boot.cml](repl_boot.cml):
This file gives the CakeML REPL multi-line input and file loading
capabilities.

[sexprBootstrap32Script.sml](sexprBootstrap32Script.sml):
Produces an sexp print-out of the bootstrap translated compiler
definition for the 32-bit version of the compiler.

[sexprBootstrap64Script.sml](sexprBootstrap64Script.sml):
Produces an sexp print-out of the bootstrap translated compiler
definition for the 64-bit version of the compiler.

[test-hello.cml](test-hello.cml):
A hello world program used for testing that the bootstrapped
compiler was built succesfully.

[to_dataBootstrapScript.sml](to_dataBootstrapScript.sml):
Evaluate the 32-bit version of the compiler down to a DataLang
program.

[to_lab_x64BootstrapScript.sml](to_lab_x64BootstrapScript.sml):
Evaluate the 64-bit version of the compiler down to a LabLang
program (an assembly program).

[x64BootstrapScript.sml](x64BootstrapScript.sml):
Evaluate the final part of the 64-bit version of the compiler
into machine code for x64.

[x64_config_encScript.sml](x64_config_encScript.sml):
Encoding of compiler state
