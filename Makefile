DAFNYCC=dafny

all: symexec.exe

symexec.exe: symexec.dfy scheduler.dfy executor.dfy
	$(DAFNYCC) $^
