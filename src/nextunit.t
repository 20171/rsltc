<SPECIAL>@ {
  FILE * next;

  BEGIN (INITIAL);
  next = (FILE *) NextFile ();
  if (next == (FILE *) 0) {
    yyterminate ();
  }
  else {
    yy_delete_buffer (YY_CURRENT_BUFFER);
    yy_switch_to_buffer (yy_create_buffer (next, YY_BUF_SIZE));
    return nextunit;
  }
}
