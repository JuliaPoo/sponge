ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqtop))/
endif

%: Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

seriousclean:
	rm -rf src/g_egg.ml
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' -o -name 'Makefile.coq' -o -name 'Makefile.coq.conf' -o -name '*.cmt' -o -name '*.cmti' -o -name '*.cmi' -o -name '*.cmt' -o -name '*.cmx' -o -name '*.d' -o -name '*.o' -o -name '*.a' -o -name '*.cmx' -o -name '*.cmxa' -o -name '*.cmxs' \) -delete

-include Makefile.coq
