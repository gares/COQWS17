# COQC=/home/gares/COQ/coq/bin/coqc
# MC=/home/gares/INRIA/MathComp/math-comp/mathcomp
COQDOC=coqdoc/bin/coqdoc
WEB=/media/sophia/www-sop/teams/marelle/advanced-coq-16/

VS=$(wildcard *.v)
HTML=$(VS:%.v=%.html)


all: coqdoc/bin/coqdoc $(HTML)

coqdoc/bin/coqdoc:
	git submodule init
	git submodule update
	cd coqdoc && ./configure -local && make bin/coqdoc

#upload:
#	cp $(HTML) FileSaver.js Blob.js $(WEB)


#	$(COQC) -R $(MC) mathcomp -I $(MC) $<
%.html.tmp: %.v header.html footer.html Makefile
	$(COQC)  $<
	$(COQDOC) --backend=jscoq \
		--with-header header.html \
		--with-footer footer.html \
		--parse-comments $< -o $@

test.html: test.html.tmp
	sed 's/@@COQ_PACKAGES@@//' $< > $@
lesson1.html: lesson1.html.tmp
	sed 's/@@COQ_PACKAGES@@//' $< > $@
lesson2.html: lesson2.html.tmp
	sed 's/@@COQ_PACKAGES@@//' $< > $@
lesson3.html: lesson3.html.tmp
	sed 's/@@COQ_PACKAGES@@//' $< > $@
lesson4.html: lesson4.html.tmp
	sed 's/@@COQ_PACKAGES@@//' $< > $@
lesson5.html: lesson5.html.tmp
	sed "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
lesson6.html: lesson6.html.tmp
	sed "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
lesson7.html: lesson7.html.tmp
	sed "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exercise1.html: exercise1.html.tmp
	sed -e 's/^(\*D\*).*$$/Admitted./' -e 's/@@COQ_PACKAGES@@//' $< > $@
exercise2.html: exercise2.html.tmp
	sed -e 's/^(\*D\*).*$$//' -e 's/@@COQ_PACKAGES@@//' $< > $@
exercise3.html: exercise3.html.tmp
	sed -e 's/^(\*D\*).*$$/Admitted./' -e 's/@@COQ_PACKAGES@@//' $< > $@
exercise4.html: exercise4.html.tmp
	sed -e 's/^(\*D\*).*$$/Admitted./' -e 's/@@COQ_PACKAGES@@//' $< > $@
exercise5.html: exercise5.html.tmp
	sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./' -e "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exercise5-todo.v : exercise5.v
	sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./' -e "s/@@COQ_PACKAGES@@/'math-comp'/" exercise5.v > exercise5-todo.v
exercise6.html: exercise6.html.tmp
	sed -e 's/^(\*D\*).*$$/Admitted./' -e "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exercise6-todo.v: exercise6.v
	sed -e 's/^(\*D\*).*$$//' -e "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exercise7.html: exercise7.html.tmp
	sed -e 's/^(\*D\*).*$$/Admitted./' -e "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exam.html: exam.html.tmp
	sed -e 's/^(\*A\*).*$$/Admitted./' \
		-e 's/^(\*X\*).*$$//' \
		-e 's/(\*D\*).*(\*D\*)/.../' \
		-e "s/@@COQ_PACKAGES@@/'math-comp'/" $< > $@
exam-todo.v: exam.v
	sed -e 's/^(\*A\*).*$$/Admitted./' \
		-e 's/^(\*X\*).*$$//' \
		-e 's/(\*D\*).*(\*D\*)/.../' $< > $@
