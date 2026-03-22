int main1(int d,int k){
  int e, rp, t, zl, my;
  e=73;
  rp=0;
  t=0;
  zl=0;
  my=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == d * zl;
  loop invariant rp == 0;
  loop invariant 0 <= zl <= e;
  loop invariant my == d + zl * (e - rp);
  loop assigns t, zl, my;
*/
while (1) {
      if (!(zl<e)) {
          break;
      }
      t += d;
      zl += 1;
      my = my+e-rp;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant my - e == d + 5256;
  loop invariant 2*rp == (73 - e) * (72 + e);
  loop invariant 0 <= e <= 73;
  loop assigns e, my, rp;
*/
while (e!=0) {
      e = e - 1;
      my = my - 1;
      rp = rp + e;
  }
}