int main1(){
  int l, m1x, bif, e, rgt, jiq, eqyi;
  l=1;
  m1x=0;
  bif=1;
  e=0;
  rgt=l;
  jiq=-1;
  eqyi=m1x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == ((bif - 1) * bif * (2 * bif - 1)) / 6;
  loop invariant rgt == l + 2 * (bif - 1);
  loop invariant jiq == 2 * bif - 3;
  loop invariant eqyi == (bif * (bif + 1)) / 2 - 1;
  loop invariant l == 1;
  loop assigns e, rgt, bif, jiq, eqyi;
*/
while (bif<=l) {
      e = e+bif*bif;
      rgt += 2;
      bif += 1;
      jiq += 2;
      eqyi = eqyi + bif;
  }
}