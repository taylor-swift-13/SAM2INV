int main1(int s,int d){
  int i1m, xt, yh, xbmy, jj;
  i1m=62;
  xt=0;
  yh=3;
  xbmy=16;
  jj=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i1m == 62;
  loop invariant xbmy == 16 + 6 * (jj - 6);
  loop invariant (6 <= jj);
  loop invariant (jj <= i1m + 1);
  loop invariant (yh == 3*jj*jj - 23*jj + 33);
  loop invariant xt >= 0;
  loop invariant s >= \at(s, Pre);
  loop invariant d == \at(d, Pre) &&
                   s >= \at(s, Pre) &&
                   xt >= 0 &&
                   yh >= 0 &&
                   xbmy >= 16;
  loop assigns xt, yh, jj, xbmy, s;
*/
while (1) {
      if (jj>i1m) {
          break;
      }
      xt = xt + yh;
      yh += xbmy;
      jj += 1;
      xbmy += 6;
      s = s+yh+xt;
  }
}