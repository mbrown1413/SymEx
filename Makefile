
DAFNY_CC=dafny  # Dafny compiler
CS_CC=mcs  # C# Compiler

# Path to "Microsoft.Z3.dll". Leave blank if Microsoft.Z3.dll is in (or linked
# from) the current directory.
Z3PATH=

# Ignore same C# warnings that Dafny does
# warning CS0219: Variable assigned but never used
# warning CS0164: Label is never referenced
# warning CS1717: Assignment made to same variable
CS_IGNORED_WARNINGS=/nowarn:0164 /nowarn:0219 /nowarn:1717

all: symexec.exe

symexec.exe: symexec.cs satNative.cs
	$(CS_CC) $(CS_IGNORED_WARNINGS) -r:$(Z3PATH)Microsoft.Z3.dll -r:System.Numerics.dll $^

# Compile Dafny -> C#, but not C# -> .NET, since we need to add library
# flags ourself
symexec.cs: symexec.dfy scheduler.dfy executor.dfy sat.dfy satNative.cs
	-$(DAFNY_CC) /verifyAllModules /compile:1 /spillTargetCode:1 /out:$@ $^

clean:
	-rm symexec.cs symexec.exe symexec.exe.mdb

.PHONY: clean
