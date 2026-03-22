int main1(){
  int jq4, n, a, uu, vfg, y0;
  jq4=(1%32)+17;
  n=0;
  a=0;
  uu=0;
  vfg=(1%18)+5;
  y0=jq4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vfg + n == 6;
  loop invariant 0 <= n;
  loop invariant uu == n;
  loop invariant y0 == 18 + n*(n+1)/2;
  loop invariant a == uu;
  loop invariant y0 == jq4 + a*(a+1)/2;
  loop invariant vfg >= 0;
  loop assigns vfg, n, a, uu, y0;
*/
while (1) {
      if (!(vfg>0)) {
          break;
      }
      vfg = vfg - 1;
      n = n+1*1;
      a = a+1*1;
      uu = uu+1*1;
      y0 = y0 + a;
  }
}