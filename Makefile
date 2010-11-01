.PHONY: doc web

all:
	echo "Targets: clean, wc"

clean:
	rm -f *.fasl *~
	make -C doc clean

wc:
	wc -l *.lisp

doc:
	make -C doc

web: doc
	cp doc/pileup.html tmp.html
	git checkout gh-pages
	mv tmp.html index.html
