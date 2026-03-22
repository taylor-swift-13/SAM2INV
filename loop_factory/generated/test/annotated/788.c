int main1(){
  int l5vl, h6rc, h77, txyg;
  l5vl=1+11;
  h6rc=l5vl;
  h77=l5vl;
  txyg=1+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h77 == l5vl + (l5vl - h6rc) * txyg;
  loop invariant h6rc >= 0;
  loop assigns h77, h6rc;
*/
while (h6rc>0) {
      h77 += txyg;
      h6rc = h6rc - 1;
  }
}