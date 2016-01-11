COQC=/home/gares/COQ/coq/bin/coqc
MC=/home/gares/INRIA/MathComp/math-comp/mathcomp
COQDOC=/home/gares/work-area/jscoq-coq/bin/coqdoc
WEB=/media/sophia/www-sop/teams/marelle/advanced-coq-16/

HTML=test.html lesson1.html

all: $(HTML)

upload:
	cp $(HTML) FileSaver.js Blob.js $(WEB)


%.html: %.v header.html footer.html Makefile
	$(COQC) -R $(MC) mathcomp -I $(MC) $<
	$(COQDOC) --backend=jscoq --with-header header.html --with-footer footer.html \
		--parse-comments $<
