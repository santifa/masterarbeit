ocamlc -c insert_sort.mli
ocamlc -c insert_sort.ml
ocamlc -c test_sort.ml
ocamlc -o test_sort insert_sort.cmo test_sort.cmo
