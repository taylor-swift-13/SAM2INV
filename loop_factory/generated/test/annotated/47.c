int main1(int a,int s){
  int o3, wc, vu, ise, n, xg;
  o3=166;
  wc=0;
  vu=0;
  ise=2;
  n=0;
  xg=wc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4 * xg == vu;
  loop invariant n == vu;
  loop invariant xg >= 0;
  loop invariant ise == 2 + vu;
  loop invariant a == \at(a, Pre) + (5 * xg * (xg + 1)) / 2;
  loop invariant vu >= 0;
  loop invariant vu <= o3 + 3;
  loop assigns ise, vu, n, xg, a;
*/
while (vu<o3) {
      ise += 4;
      vu += 4;
      n += 4;
      xg++;
      a = a + vu;
      a = a + xg;
  }
}