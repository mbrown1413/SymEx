
SymEx is a verified symbolic execution engine written in Dafny, a language with
the ability to statically prove properties about programs.


## Requirements

### Mono

The 64-bit mono build is required, because we need to interface with Z3.

TODO

We've tested with:

  * Mono Version 5.3.0 amd64 on Mac
  * Mono Version 4.2.1 amd64 on Linux

### Dafny

See: [Dafny build instructions](https://github.com/Microsoft/dafny/wiki/INSTALL)

If you didn't install Dafny globally, you will need to make the `dafny`
executable available when compiling. If you downloaded the binary release, you
should put the binaries directory in your PATH like this:

    $ export PATH=$PATH:/<dafny-directory>/Binaries/

Put the above in your `.bashrc` to make the change permanent.

We've tested with:

  * Dafny Version 1.9.9.40414 on Mac and Linux

### Z3

Download the latest from their
[releases](https://github.com/Z3Prover/z3/releases) and unzip it.

Alternatively, they have instructions to [build from
source](https://github.com/Z3Prover/z3). Make sure to include `--dotnet` to
compile the C# bindings.

When compiling SymEx, `Microsoft.Z3.dll` needs to be available. This file will
be in `z3-<version>/bin/' in the binary release, or in `build/` if you compiled
from source. The simplest way to make this available is link to it in the SymEx
directory:

    $ cd SymEx/
    $ ln -s /path/to/Microsoft.Z3.dll

## Compiling

Compile:

  $ make

You may see errors like this:

    satNative.cs(8,17) : error CS0234: The type or namespace name `Z3' does not exist in the namespace `Microsoft'. Are you missing an assembly reference?

Before panicking that Z3 could not be found, see if `symexec.exe` exists. Dafny
may not be able to find `Microsoft.Z3.dll` when it generates the C# code, but
we compile the C# code afterwards in a separate step that looks for
`Microsoft.Z3.dll` in the current directory.

## Running

    $ mono symexec.exe

or

    $ ./symexec.exe
