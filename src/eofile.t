<<EOF>> {
  BEGIN (SPECIAL);
  unput ('@');
  return eofile;
}
