# Take opam config if available.
ifeq (, $(shell which opam 2> /dev/null))
$(warning "We recommend using opam for dependencies.")
PREFIX   = /usr/local
BINDIR   = $(PREFIX)/bin
LIBDIR   = $(PREFIX)/lib
else
PREFIX   = $(shell opam config var prefix)
BINDIR   = $(shell opam config var bin)
LIBDIR   = $(shell opam config var lib)
endif

# Editors directory.
EMACSDIR = $(PREFIX)/emacs/site-lisp
VIMDIR   = $(HOME)/.vim

# Version.
VERSION  = devel

# Main target.
.PHONY: all
all: bin

.PHONY: bin
bin: src/config.ml
	@dune build

# Documentation target.
.PHONY: doc
doc:
	@dune build @doc

# Configuration file.
src/config.ml: GNUmakefile
	@echo "let path = [\"$(LIBDIR)/pml2\"]" > $@

# Checks on the source code.
check:
	# FIXMES/TODOS
	@f=`grep FIXME */*.ml */*.mli */*.pml */*/*.pml  | wc -l`;\
	 ft=`grep FIXME */*.ml */*.mli */*.pml */*/*.pml | grep -P -v '#[0-9]+' | wc -l`;\
	 echo FIXME: $$ft/$$f '(without ticket/all)'
	@grep FIXME */*.ml */*.mli */*.pml */*/*.pml -n | grep -P -v '#[0-9]+' || true
	@f=`grep TODO */*.ml */*.mli */*.pml */*/*.pml | wc -l`;\
	 ft=`grep TODO */*.ml */*.mli */*.pml */*/*.pml | grep -P -v '#[0-9]+' | wc -l`;\
	 echo TODO: $$ft/$$f '(without ticket/all)'
	@grep TODO */*.ml */*.mli */*.pml */*/*.pml -n | grep -P -v '#[0-9]+' || true
	# TAB/LINES TOO LONG
	@echo Lines with TAB:
	@grep -P "\t" */*.ml */*.mli; true
	@echo Lines too long:
	@grep -n '^.\{80\}' */*.ml */*.mli; true

# Lib target (PML handles the dependencies).
.PHONY: lib
LIB_FILES = $(wildcard lib/*.pml)
lib: bin $(LIB_FILES)
	@for f in $(LIB_FILES); do dune exec -- pml --quiet $$f || break ; done

# Test target.
.PHONY: test
TEST_FILES = $(wildcard examples/*.pml test/*.pml test/*/*.pml)
test: bin lib $(TEST_FILES)
	@for f in $(TEST_FILES); do echo $$f; dune exec -- pml --quiet $$f || break ; done

# target to mesure time
.PHONY: time
time:
	make libclean
	time make lib test

# Cleaning targets.
clean: libclean
	@dune clean

libclean:
	@find . -name \*.pmi -exec rm {} \;
	@find . -name \*.vo -exec rm {} \;
	@find . -name \*.vo.aux -exec rm {} \;
	@find . -name \*.glob -exec rm {} \;
	@find . -name \*.agdai -exec rm {} \;

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name \#\* -exec rm {} \;
	@find . -type f -name .\#\* -exec rm {} \;
	@rm -f src/config.ml

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
install_vim: editors/vim/indent/pml.vim editors/vim/syntax/pml.vim
ifeq ($(wildcard $(VIMDIR)/.),)
	@echo -e "\e[36mWill not install vim mode.\e[39m"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/indent
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/pml.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/indent/pml.vim $(VIMDIR)/indent
	install -m 644 editors/vim/ftdetect/pml.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
endif

# Install for the emacs mode (system-wide).
.PHONY: install_emacs
install_emacs: editors/emacs/pml2-mode.el
ifeq ($(wildcard $(EMACSDIR)/.),)
	@echo -e "\e[36mWill not install emacs mode.\e[39m"
else
	install -d $(EMACSDIR)
	install -m 644 editors/emacs/pml2-mode.el $(EMACSDIR)
	install -m 755 editors/emacs/pml2-indent.sh $(BINDIR)/pml2-indent
	@echo -e "\e[36mEmacs mode installed.\e[39m"
endif

# Install.
.PHONY: install
install: bin
	@dune install

# Release.
.PHONY: release
release: distclean
	git push origin
	git tag -a pml_$(VERSION)
	git push origin pml_$(VERSION)
