SHELL = /bin/sh

srcdir = src
top_srcdir = .

ifdef DEBIAN_BUILD_ROOT
prefix = $(DEBIAN_BUILD_ROOT)/usr
else
prefix = /usr
endif

exec_prefix = ${prefix}

bindir = ${exec_prefix}/bin
sbindir = ${exec_prefix}/sbin
libexecdir = ${exec_prefix}/libexec
datadir = ${prefix}/share
sysconfdir = ${prefix}/etc
sharedstatedir = ${prefix}/com
localstatedir = ${prefix}/var
libdir = ${exec_prefix}/lib
infodir = ${prefix}/info
mandir = ${prefix}/man
includedir = ${prefix}/include
oldincludedir = /usr/include
pkgdatadir = ${datadir}/rsltc
ifdef DEBIAN_BUILD_ROOT
pkgdocdir = ${datadir}/doc/rsltc
else
pkgdocdir = ${datadir}/rsltc/doc
endif
pkglatexdir = ${datadir}/texmf/tex/latex/rsltc
pkglibdir = ${libdir}/rsltc
pkgincludedir = $(includedir)/rsltc
top_builddir = .

install_sh = $(SHELL) $(top_srcdir)/install-sh
install_sh_DATA = $(install_sh) -c -m 644
install_sh_PROGRAM = $(install_sh) -c
install_sh_SCRIPT = $(install_sh) -c
INSTALL_PROGRAM = $(install_sh_PROGRAM)
INSTALL_DATA = $(install_sh_DATA)
INSTALL_SCRIPT = $(install_sh_SCRIPT)

EXEEXT = 
OBJEXT = o
PATH_SEPARATOR = :
CC = gcc-3.4
CXX = g++-3.4
LEX = flex
LEXLIB = -lfl
LEX_OUTPUT_ROOT = lex.yy
PACKAGE = rsltc
YACC = bison -y
ifdef RPM_BUILD_ROOT
lispdir = $(RPM_BUILD_ROOT)/usr/share/emacs/site-lisp
else
lispdir = ${datadir}/emacs/site-lisp
endif

VERSION_NUM = "\"2.6\""
MAKE_DATE = "\"$(shell date)\""

TOKENS = filename.t eofile.t nextunit.t char_lit.t id.t int_lit.t \
  real_lit.t tex t_lit.t
GENTLE_G = ast.g env.g ext.g print.g grammar.g objects.g types.g \
  values.g cc.g pp.g cpp.g c_ast.g c_unparse.g c_decl.g sml.g \
  pvs_ast.g pvs_aux.g pvs_col_sort.g pvs_gen_ast.g pvs_gen_code.g pvs.g \
  sal_ast.g sal_aux.g sal_cc_aux.g sal_decl_sort.g sal.g sal_gen_ast.g \
  sal_gen_code_aux.g sal_gen_code_bindings.g sal_gen_code.g \
  sal_gen_code_types.g sal_global_vars.g sal_print.g sal_type_fixed_point.g \
  fdr.g fdr_ast.g fdr_gen_ast.g fdr_gen_code.g ltl_out.g trans_delta.g
C_C = errmsg.c files.c idents.c strings.c ccgen.c main.c pos.c

bin_PROGRAMS = rsltc
rsltc_SOURCES = $(TOKENS) $(GENTLE_G) $(C_C)
rsltc_LISP = rsltc.el rsl-mode.el rslconvert.el tokenise.el \
  sml-font.el sml-menus.el sml-mode.el sml-proc.el sml-site.el 
rsltc_CC = RSL_list.cc RSL_set.cc cpp_RSL.cc cpp_list.cc \
  RSL_map.cc RSL_typs.cc cpp_io.cc  cpp_set.cc
rsltc_H = RSL_comp.h RSL_map.h RSL_text.h cpp_io.h cpp_test.h \
  RSL_prod.h RSL_typs.h cpp_list.h \
  RSL_list.h RSL_set.h cpp_RSL.h cpp_set.h
rsltc_HTML = \
ug.html     ug_2.html	ug_31.html  ug_43.html	ug_55.html  ug_67.html \
ug_0.html   ug_20.html	ug_32.html  ug_44.html	ug_56.html  ug_68.html \
ug_1.html   ug_21.html	ug_33.html  ug_45.html	ug_57.html  ug_69.html \
ug_10.html  ug_22.html	ug_34.html  ug_46.html	ug_58.html  ug_7.html \
ug_11.html  ug_23.html	ug_35.html  ug_47.html	ug_59.html  ug_70.html \
ug_12.html  ug_24.html	ug_36.html  ug_48.html	ug_6.html   ug_71.html \
ug_72.html  ug_73.html  ug_74.html  ug_75.html  ug_76.html  ug_77.html \
ug_78.html \
ug_13.html  ug_25.html	ug_37.html  ug_49.html	ug_60.html  ug_8.html \
ug_14.html  ug_26.html	ug_38.html  ug_5.html	ug_61.html  ug_9.html \
ug_15.html  ug_27.html	ug_39.html  ug_50.html	ug_62.html  ug_toc.html \
QSI.png		 UML2RSL_f11d.png  UML2RSL_f18a.png	blank.png \
UML2RSL_f1.png	 UML2RSL_f14.png   UML2RSL_f1a_SCA.png	next.png \
UML2RSL_f10.png  UML2RSL_f15.png   UML2RSL_f21a.png	previous.png \
UML2RSL_f11.png  UML2RSL_f17.png   UML2RSL_f6.png	up.png \
ascii.png
rsltc_PDF = ug.pdf
rsltc_DOC = doc/HISTORY LICENSE README doc/README.help doc/RSL.changes doc/design.tex doc/design.ps.gz 
rsltc_PVS = rsl_prelude.pvs rsl_prelude.prf
rsltc_SML = rslml.cm rslml.sml
rsltc_LATEX = rslenv.sty
rsltc_UML2RSL = \
  Association.class   EquivalentTypes.class	   Operation.class \
  Attribute.class     EquivalentTypesTable.class   Pair.class \
  Clase.class	      FormalParameter.class	   RSLKeywordTable.class \
  ClassDiagram.class  Generalization.class	   RecAlias.class \
  Dependency.class    Instantiation.class	   UML2RSL.class \
  End.class	      Multiplicity.class           UML2RSL.java
rsltc_SAL = \
  sal_make bool_cc_prelude cc_type_prelude int_cc_prelude int_prelude \
  map_cc_prelude map_prelude set_cc_prelude set_prelude array_cc_prelude 
rsltc_SAL_sh = sal_wfc_check

mkinstalldirs = $(SHELL) $(top_srcdir)/mkinstalldirs
bin_PROGRAMS = rsltc$(EXEEXT)
PROGRAMS = $(bin_PROGRAMS)


DIST_SOURCES = $(rsltc_SOURCES)
SOURCES = $(rsltc_SOURCES)

# rules

all: rsltc

rsltc:
	cd src && $(MAKE)

install:	install-prog install-lisp install-libs install-ug \
	install-doc install-pvs install-sml install-latex install-sal \
	install-UML2RSL

install-prog:
	$(mkinstalldirs) $(bindir)
	$(INSTALL_PROGRAM) src/rsltc $(bindir)
	$(INSTALL_PROGRAM) rslcomp $(bindir)

install-lisp:
	$(mkinstalldirs) $(lispdir)
	for x in $(rsltc_LISP) ; do \
	  $(INSTALL_DATA) lisp/$$x $(lispdir) ; \
	done;

install-libs:
	$(mkinstalldirs) $(pkgincludedir)
	for x in $(rsltc_H) ; do \
	  $(INSTALL_DATA) cpp/$$x $(pkgincludedir) ; \
	done;
	for x in $(rsltc_CC) ; do \
	  $(INSTALL_DATA) cpp/$$x $(pkgincludedir) ; \
	done;

install-ug:
	$(mkinstalldirs) $(pkgdocdir)/html
	for x in $(rsltc_HTML) ; do \
	  $(INSTALL_DATA) ug/$$x $(pkgdocdir)/html ; \
	done;
	cd $(pkgdocdir)/html && ln -fs ug.html index.html
	for x in $(rsltc_PDF) ; do \
	  $(INSTALL_DATA) ug/$$x $(pkgdocdir) ; \
	done;

install-doc:
	$(mkinstalldirs) $(pkgdocdir)
	for x in $(rsltc_DOC) ; do \
	  $(INSTALL_DATA) $$x $(pkgdocdir) ; \
	done;

install-pvs:
	$(mkinstalldirs) $(pkgdatadir)/pvs
	for x in $(rsltc_PVS) ; do \
	  $(INSTALL_DATA) pvs/$$x $(pkgdatadir)/pvs ; \
	done;

install-sml:
	$(mkinstalldirs) -m 777 $(pkgdatadir)/sml
	for x in $(rsltc_SML) ; do \
	  $(INSTALL_DATA) sml/$$x $(pkgdatadir)/sml ; \
	done;

install-sal:
	$(mkinstalldirs) $(pkgdatadir)/sal
	for x in $(rsltc_SAL) ; do \
	  $(INSTALL_DATA) sal/$$x $(pkgdatadir)/sal ; \
	done;
	for x in $(rsltc_SAL_sh) ; do \
	  $(INSTALL_SCRIPT) sal/$$x $(pkgdatadir)/sal ; \
	done;

install-latex:
	$(mkinstalldirs) $(pkglatexdir)
	for x in $(rsltc_LATEX) ; do \
	  $(INSTALL_DATA) latex/$$x $(pkglatexdir) ; \
	done;

install-UML2RSL:
	$(mkinstalldirs) $(pkgdatadir)/UML2RSL
	for x in $(rsltc_UML2RSL) ; do \
	  $(INSTALL_DATA) UML2RSL/$$x $(pkgdatadir)/UML2RSL ; \
	done;

clean:
	cd src && $(MAKE) clean
	
uninstall:	uninstall-prog uninstall-lisp uninstall-libs uninstall-main

uninstall-prog:
	rm -rf $(bindir)/rsltc
	rm -rf $(bindir)/rslcomp

uninstall-lisp:
	for x in $(rsltc_LISP) ; do \
	  rm -rf $(lispdir)/$$x ; \
	done;

uninstall-libs:
	rm -rf $(pkgincludedir)

uninstall-main:
	rm -rf $(pkgdatadir)

uninstall-ug:
	rm -rf $(pkgdocdir)/html
	for x in $(rsltc_PDF) ; do \
	  rm -rf $(pkgdocdir)/$$x ; \
	done;

uninstall-doc:
	rm -rf $(pkgdocdir)

uninstall-pvs:
	rm -rf $(pkgdatadir)/pvs

uninstall-sml:
	rm -rf $(pkgdatadir)/sml

uninstall-sal:
	rm -rf $(pkgdatadir)/sal

uninstall-latex:
	rm -rf $(pkglatexdir)

uninstall-UML2RSL:
	rm -rf $(pkgdatadir)/UML2RSL




# Tell versions [3.59,3.63) of GNU make to not export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:
