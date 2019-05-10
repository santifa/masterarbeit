


schedule: masterarbeit.org
	emacs -batch $< -f org-latex-export-to-pdf; \
  rm masterarbeit.tex

thesis:

velisarios:
	./bootstrap.sh

simulate:
  cd Velisarios/runtime && ./Simul.native -max 100

run:
  cd Velisarios/runtime && ./run.sh
