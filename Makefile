COQC=coqc
MC=
WEB=/media/sophia/www-sop/teams/marelle/advanced-coq-16-17/

VS=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard *.v)))
EX=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard exercise*.v)))
FILES=$(VS:%.v=%.html) $(VS) $(EX:%.v=%-todo.v)

all: jscoq udoc/udoc.byte cheat-sheet/cheatsheet.pdf $(FILES)

jscoq.orig:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 jscoq
	cd jscoq && git checkout c219bd7e4b207846a607ce5a19513412d826ce7a
	mv jscoq jscoq.orig

jscoq.tgz:
	rm -rf jscoq
	cp -rf jscoq.orig jscoq
	cd jscoq/coq-pkgs/; for X in `ls`; do\
		if [ $$X != Coq            -a\
		     $$X != mathcomp       -a\
		     $$X != math-comp.json -a\
		     $$X != coq-arith.json -a\
		     $$X != coq-base.json  -a\
		     $$X != coq-reals.json -a\
		     $$X != init.json      -a\
		     $$X != bcache         -a\
		     $$X != bcache.list      ]; then \
		     rm -rf $$X; \
		fi; done
	patch -p1 < jscoq.patch
	rm -rf jscoq/.git
	tar -czf jscoq.tgz jscoq/
	rm -rf jscoq

jscoq: jscoq.tgz
	tar -xzf jscoq.tgz
	touch jscoq

udoc/udoc.byte: udoc.patch
	$(MAKE) check-ocaml-ver-4.02.0
	rm -rf udoc
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && git checkout 11fa04a621e8f8bc156430da4f0d3c10d8585ab3
	cd udoc && patch -p1 < ../udoc.patch
	cd udoc && make

cheat-sheet/cheatsheet.pdf: cheat-sheet/cheatsheet.tex
	make -C cheat-sheet

check-ocaml-ver-%:
	@ V=`(echo -n '2 '; ocamlc -version; echo -n '1 '; echo $*) \
	  | sed 's/\./ /g' \
	  | sort -n -k 4 -k 3 -k 2 -k 1 | head -n 1 | cut -d ' ' -f 1)`; \
	if `test $$V = 2`; then echo "OCaml must be >= $*"; false; fi

upload: $(FILES) cheat-sheet/cheatsheet.pdf jscoq.tgz
	mkdir -p $(WEB)
	[ -d $(WEB)/jscoq ] || tar -xzf jscoq.tgz -C $(WEB)
	cp $(FILES) FileSaver.js Blob.js local.css cheat-sheet/cheatsheet.pdf \
		$(WEB)

%.html.tmp: %.v footer Makefile udoc/udoc.byte
	@cat $< footer > $*tmp.v
	@# if does not work, then html ok but no links
	-$(COQC) $*tmp.v > /dev/null
	@# -$(COQC) -R $(MC) mathcomp -I $(MC) $<
	@./udoc/udoc.byte -t $* $*tmp.v -o $@
	@sed -i -e 's?^ *<h1>$*tmp</h1>??' $@
	@sed -i -e 's?^ *<title.*?<title>$*</title>?' $@
	@sed -i -e 's?^ *<h1>$*</h1>??' $@
	@sed -i -e 's?</title>?</title><link rel="stylesheet" href="local.css" />?' $@
	@sed -i -e 's?</title>?</title><script src="Blob.js" type="text/javascript"></script>?' $@
	@sed -i -e 's?</title>?</title><script src="FileSaver.js" type="text/javascript"></script>?' $@
	@rm -f $<.tmp

run: jscoq
	@echo "Go to: http://localhost:8000/lesson1.html"
	python3 -m http.server 8000 || python -m SimpleHTTPServer 8000


test.html: test.html.tmp
	@mv $< $@

# Lessons
lesson1.html: lesson1.html.tmp
	@mv $< $@
lesson2.html: lesson2.html.tmp
	@mv $< $@
lesson3.html: lesson3.html.tmp
	@mv $< $@
lesson4.html: lesson4.html.tmp
	@mv $< $@
lesson5.html: lesson5.html.tmp
	@mv $< $@
lesson6.html: lesson6.html.tmp
	@mv $< $@
lesson7.html: lesson7.html.tmp
	@mv $< $@
	
# Exercises
exercise1.html: exercise1.html.tmp
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise1-todo.v: exercise1.v
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise2.html: exercise2.html.tmp
	@sed -e 's/^(\*D\*).*$$//' -e 's/^(\*A\*).*$$/Admitted./' $< > $@
exercise2-todo.v: exercise2.v
	@sed -e 's/^(\*D\*).*$$//' -e 's/^(\*A\*).*$$/Admitted./' $< > $@
exercise3.html: exercise3.html.tmp
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise3-todo.v: exercise3.v
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise4.html: exercise4.html.tmp
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise4-todo.v: exercise4.v
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise5.html: exercise5.html.tmp
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  $< > $@
exercise5-todo.v : exercise5.v
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  exercise5.v > exercise5-todo.v
exercise6.html: exercise6.html.tmp
	@sed -e 's/^(\*D\*).*$$/Admitted./' $< > $@
exercise6-todo.v: exercise6.v
	@sed -e 's/^(\*D\*).*$$//' $< > $@
exercise7.html: exercise7.html.tmp
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./' $< > $@
exercise7-todo.v : exercise7.v
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./' exercise7.v > exercise7-todo.v
	
# Exam
exam.html: exam.html.tmp
	@sed -e 's/^(\*A\*).*$$/Admitted./' \
		-e 's/(\*a\*).*$$/admit./' \
		-e '/^(\*X\*).*$$/d' \
		-e 's/(\*D\*).*(\*D\*)/.../' \
		$< > $@
exam-todo.html: exam-todo.html.tmp
	@sed -e 's/^(\*A\*).*$$/Admitted./' \
		-e 's/(\*a\*).*$$/admit./' \
		-e '/^(\*X\*).*$$/d' \
		-e 's/(\*D\*).*(\*D\*)/.../' \
		$< > $@
exam-todo.v: exam.v
	@sed -e 's/^(\*A\*).*$$/Admitted./' \
		-e 's/(\*a\*).*$$/admit./' \
		-e '/^(\*X\*).*$$/d' \
		-e 's/(\*D\*).*(\*D\*)/.../' $< > $@
