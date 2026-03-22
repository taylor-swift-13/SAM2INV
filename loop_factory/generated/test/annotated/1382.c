int main1(){
  int dl, qb, z26, lfm, a, ap;
  dl=(1%35)+15;
  qb=(1%35)+15;
  z26=1;
  lfm=0;
  a=0;
  ap=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (dl + qb <= 32);
  loop invariant dl > 0;
  loop invariant qb > 0;
  loop invariant a <= 0;
  loop invariant ap >= 1;
  loop assigns dl, qb, z26, lfm, a, ap;
*/
while (dl!=qb) {
      if (dl>qb) {
          dl = dl - qb;
          z26 = z26 - lfm;
          a = a - ap;
      }
      else {
          qb -= dl;
          lfm -= z26;
          ap = ap - a;
      }
      z26 = z26*2+5;
  }
}