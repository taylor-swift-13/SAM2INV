int main1(int n){
  int gn, f, d, pa, ma0;
  gn=n+5;
  f=0;
  d=0;
  pa=0;
  ma0=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pa == f % 2;
  loop invariant gn == \at(n, Pre) + 5;
  loop invariant ma0 == 16 + (f * (f + 1)) / 2;
  loop invariant d <= f * ma0;
  loop invariant -d <= f * ma0;
  loop invariant 0 <= f && (gn <= 0 || f <= gn);
  loop assigns f, pa, d, ma0;
*/
while (f < gn) {
      pa = 1 - pa;
      f = f + 1;
      d = d + ma0 * (2 * pa - 1);
      ma0 += f;
  }
}