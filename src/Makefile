# Solaris makefile for RSL type checker
#
# 5 February 1998, raise@iist.unu.edu

VERSION_NUM = "\"2.6\""
MAKE_DATE = "\"$(shell date)\""
ifndef GENTLE_DIR
GENTLE_DIR = /usr/share/gentle
endif
GENTLE = $(GENTLE_DIR)/gentle/gentle
GRTS = $(GENTLE_DIR)/gentle/grts.o
REFLEX = $(GENTLE_DIR)/reflex/reflex
LEX_YY = lex.yy
GEN_TAB = gen.tab
LEX = flex
YACC = bison
CC = gcc 
# CC = gcc -m32 # force 32-bit arch on 64bits machine
RM_CMD = rm -f
PGM = rsltc
FILES_FLAGS =
CFLAGS = -DRSLTC_MAKE_DATE=${MAKE_DATE} -DRSLTC_VERSION=${VERSION_NUM}
LDFLAGS = -static
BLOCKS = COMMENTS.b LEXDEF.b LEXFUNC.b LITBLOCK.b

include std_make

