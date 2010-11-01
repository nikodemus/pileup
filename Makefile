all:
	echo "Targets: clean, wc"

clean:
	rm -f *.fasl *~

wc:
	wc -l *.lisp
