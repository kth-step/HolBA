#OTT = ott
OTT = ../../../../ott/bin/ott

ott/birScript.sml: ott/bir.ott
	cd ott && $(OTT) -o birScript.sml bir.ott

ott/bir.tex: ott/bir.ott
	cd ott && $(OTT) -o bir.tex -tex_show_meta false bir.ott

ott/bir.pdf: ott/bir.tex
	cd ott && pdflatex bir.tex

hol: ott/birScript.sml
	Holmake -r -I ott

.PHONY: hol
