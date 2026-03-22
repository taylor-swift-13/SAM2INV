int main1(){
  int li, jrf, g94, kw, nbc, qj70, q;
  li=1-1;
  jrf=0;
  g94=2;
  kw=2;
  nbc=0;
  qj70=5;
  q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == jrf;
  loop invariant 0 <= jrf <= li;
  loop invariant 0 <= g94 <= qj70;
  loop invariant 0 <= nbc;
  loop invariant kw >= 2;
  loop invariant g94 + nbc >= 2;
  loop assigns g94, jrf, nbc, kw, q;
*/
for (; jrf<li; jrf++) {
      if (!(!(jrf%3==0))) {
          if (g94>0) {
              g94 = g94 - 1;
              nbc++;
          }
      }
      else {
          if (g94<qj70) {
              g94 += 1;
              kw++;
          }
      }
      q += 1;
  }
}