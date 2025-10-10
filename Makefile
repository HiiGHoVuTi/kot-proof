all: Makefile.coq
	export TIMED
	@+$(MAKE) -f Makefile.coq all

html: all Makefile.coq
	@+$(MAKE) -f Makefile.coq html
	mv html/*.html website
	rm -rf html

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

SWITCH_NAME:=kot-proof

install-deps:
	@opam switch list | grep "$(SWITCH_NAME)" || opam switch create $(SWITCH_NAME) 4.14.2
	@opam update
	@if opam list --switch=$(SWITCH_NAME) --installed coq | grep -q "8.20.1" && 
	   opam list --switch=$(SWITCH_NAME) --installed coq-iris | grep -q "4.3.0" && 
	   opam list --switch=$(SWITCH_NAME) --installed coq-iris-heap-lang >/dev/null 2>&1 && 
	   opam list --switch=$(SWITCH_NAME) --installed coq-aac-tactics >/dev/null 2>&1; 
	then 
		echo "Dependencies are already satisfied."; 
	else 
		opam exec --switch=$(SWITCH_NAME) -- opam install -y coq.8.20.1 coq-iris.4.3.0 coq-iris-heap-lang coq-aac-tactics; 
	fi

install: all
	@+$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all html clean force  
