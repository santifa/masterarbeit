


schedule: masterarbeit.org
	emacs -batch $< -f org-latex-export-to-pdf; \
  rm masterarbeit.tex

thesis:

velisarios:
	./bootstrap.sh
