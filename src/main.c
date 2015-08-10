/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#include <stdlib.h>
#include <stdio.h>
#include "files.h"


extern FILE *yyin;

extern void ROOT();

void PrintVersion() {
  char msg[200];

#ifdef RSLTC_VERSION
#ifdef RSLTC_MAKE_DATE
  if (!(PpWanted())){
    sprintf(msg, "rsltc version %s of %s\n", RSLTC_VERSION, RSLTC_MAKE_DATE);
    Putmsg(msg);
  }
#endif
#endif
}

/* cannot get this to parse so use 0 and 1 UGH!!
enum rslkind {
  timed, untimed
};

rslkind rsltype = untimed;

int IsTimed (void) {
  return (rsltype == timed);
}
*/

const int untimed = 0;
const int timed = 1;

int rsltype = 0; /* untimed */

int IsTimed (void) {
  return (rsltype == timed);
}

int ccwanted = 0; 
/* default: confidence conditions not wanted */
/* ccwanted == 1: confidence conditions for top level module only */
/* ccwanted == 2: confidence conditions for all modules */


int CcWanted (void) {
  return (ccwanted != 0);
}

int AllCcWanted (void) {
  return (ccwanted == 2);
}

int pccwanted = 0;

int PccWanted (void) {
  return (pccwanted != 0);
}

int ppwanted = 0;

int PpWanted (void) {
  return (ppwanted == 1);
}

/* Line length for pretty printing: defaults to 60 */
const int plength_default = 60;

int depswanted = 0;

int DepsWanted (void)
{
  return (depswanted == 1);
}

int graphwanted = 0;

int GraphWanted (void)
{
  return (graphwanted == 1);
}

int cppwanted = 0;

int CPPWanted (void)
{
  return (cppwanted == 1);
}

int pvswanted = 0;

int PVSWanted (void)
{
  return (pvswanted == 1);
}

int visual_cpp = 0;

int VisualCPP (void)
{
  return (visual_cpp == 1);
}

int javawanted = 0;

int JavaWanted (void)
{
  return (javawanted == 1);
}

int smlwanted = 0;

int SMLWanted (void)
{
  return (smlwanted == 1);
}

int sqlwanted = 0;

int SQLWanted (void)
{
  return (sqlwanted == 1);
}

int salwanted = 0;

int SALWanted (void)
{
  return (salwanted == 1);
}

int fdrwanted = 0;

int FDRWanted (void)
{
  return (fdrwanted == 1);
}

int main (int argc, char *argv[])
{
  int n;
  char * filename;
  int source_defined = 0;
  char msg[200];
  int plength;

  /* INITIALIZE */

  Setplength(plength_default);
  SetTime();
  n = 1;
  while (n < argc) {
    if (argv[n][0] == '-') { /* possible option */
      switch (argv[n][1]) {
      case 't' :
	if (argv[n][2] != '\0') { 
	  sprintf(msg,"invalid argument: '%s'", argv[n]);
	  ErrorUsage (msg);
	  }
	rsltype = timed;
	n++;
	break;
      case 'p' :
	if (argv[n][2] == 'l') { /* -pl option */
	  n++;
	  plength = atoi(argv[n]);
	  if(plength<30) {
	    sprintf(msg,"pretty print line length set to %s: must be at least 30", argv[n]);
	    ErrorUsage (msg);
	    }
	  else {
	    ppwanted = 1;
	    Setplength(plength); }
	  }
	else if (argv[n][2] == 'v') { /* -pv option (pvs) */
	  pvswanted = 1;
	}
	else if (argv[n][2] == 'c') { /* -pc option */
	  ccwanted = 1;
	  pccwanted = 1;
	}
	else if(argv[n][2] != '\0') {
	  sprintf(msg,"invalid argument: '%s'", argv[n]);
	  ErrorUsage (msg);
	    }
	else {  /* -p option */
	  ppwanted = 1;
	  }
	n++;
	break;
      case 'c' : 
	if (argv[n][2] == 'c') { /* -cc option */
	  ccwanted = 2;
	  }
	else if (argv[n][2] == '+') {
	  cppwanted = 1;
	}
	else if (argv[n][2] == 'p') {
	  cppwanted = 1;
	  visual_cpp = 1;
	}
	else if (argv[n][2] != '\0') {
	  sprintf(msg,"invalid argument: '%s'", argv[n]);
	  ErrorUsage (msg);
	  }
	else { /* -c option */
	  ccwanted = 1;
	  }
	n++;
	break;
     case 'f' :
	fdrwanted = 1;
	n++;
	break;
      case 'j' :
	javawanted = 1;
	n++;
	break;
      case 'g' :
	graphwanted = 1;
	n++;
	break;
      case 'd' :
	depswanted = 1;
	n++;
	break;
      case 'm' :
	smlwanted = 1;
	n++;
	break;
      case 's' :
	if (argv[n][2] == 'a') { /* -sa option (sal) */
	  salwanted = 1;
	}
	else if (argv[n][2] == 'q') { /* -sq option (sql) */
	  sqlwanted = 1;
	}
	else {
	  sprintf(msg,"invalid argument: '%s'", argv[n]);
	  ErrorUsage (msg);
	}
	n++;
	break;
      case 'v' :
	PrintVersion();
	exit(0);
      default :
	sprintf(msg,"invalid argument: '%s'", argv[n]);
	ErrorUsage (msg);
	}
      }
    else {
      if (source_defined) {
	sprintf(msg, "only one RSL file name is allowed");
        ErrorUsage (msg);
      }
      source_defined = 1;
      filename = argv [n];
      n++;
    }
  }

  if (! source_defined) {
    sprintf(msg, "you must supply an RSL file name");
    ErrorUsage (msg);
  }
  OpenFile(filename);

  /* INVOKE GENERATED PROGRAM */

  ROOT();

  /* FINALIZE */

  if ((ppwanted == 0) && (depswanted == 0)) {
    FinalMessage(ccwanted);
  }

  if (HasErrors() == 0){
    exit(0);
    }
  else exit(1);
}
