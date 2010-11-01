.PHONY: doc

all:
	echo "Targets: clean, wc"

clean:
	rm -f *.fasl *~
	make -C doc clean

wc:
	wc -l *.lisp

doc:
	make -C doc
