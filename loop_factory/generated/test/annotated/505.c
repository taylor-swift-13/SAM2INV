int main1(){
  int ol, nq, ln, axb2;
  ol=(1%36)+19;
  nq=1;
  ln=nq;
  axb2=ol;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant axb2 == ol + (ln - 1) * nq;
  loop invariant nq == 1;
  loop invariant ln <= ol;
  loop invariant ln >= 1;
  loop assigns axb2, ln;
*/
while (ln<ol) {
      ln += 1;
      axb2 = axb2 + nq;
  }
}