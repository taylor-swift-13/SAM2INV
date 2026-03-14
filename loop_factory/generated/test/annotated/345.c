int main1(){
  int v1m, xm, h3t, ro, lsx;
  v1m=1;
  xm=0;
  h3t=-1;
  ro=-2;
  lsx=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lsx == 2*h3t;
  loop invariant ro <= h3t;
  loop invariant v1m == 1;
  loop invariant h3t <= v1m;
  loop assigns ro, h3t, lsx;
*/
while (1) {
      if (!(h3t+1<=v1m)) {
          break;
      }
      if (lsx<v1m) {
          ro = h3t;
      }
      h3t++;
      lsx += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v1m - lsx == -1;
  loop invariant ro <= h3t;
  loop assigns xm, v1m, lsx;
*/
while (lsx<h3t) {
      xm = xm + ro;
      v1m = v1m + 1;
      lsx++;
  }
}