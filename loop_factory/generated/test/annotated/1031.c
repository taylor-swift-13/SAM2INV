int main1(){
  int p, e, gj, hqw, zff;
  p=1;
  e=p;
  gj=0;
  hqw=0;
  zff=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == gj + 1;
  loop invariant hqw == gj * (gj + 1) / 2;
  loop invariant p == 1;
  loop assigns gj, hqw, e;
*/
while (1) {
      if (!(e-1>=0)) {
          break;
      }
      gj += 1;
      hqw = hqw + gj;
      e += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((p == 1 && zff == 1) || (p == 0 && zff == 4));
  loop assigns p, zff;
*/
while (1) {
      if (!(p-1>=0)) {
          break;
      }
      zff += p;
      zff += zff;
      p -= 1;
  }
}