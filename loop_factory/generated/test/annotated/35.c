int main1(int m){
  int pv, ztw, tvp7, szh;
  pv=58;
  ztw=1;
  tvp7=4;
  szh=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ztw <= pv;
  loop invariant tvp7 == 4 + 6*(ztw - 1);
  loop invariant szh == 10 + 6*(ztw - 1);
  loop invariant m == \at(m, Pre) + 3*ztw*ztw + ztw - 4;
  loop invariant ztw >= 1;
  loop invariant (tvp7 - szh) == -6;
  loop invariant (szh - 10) == 6*(ztw - 1);
  loop invariant m - \at(m, Pre) == 3*(ztw - 1)*(ztw - 1) + 7*(ztw - 1);
  loop assigns m, tvp7, szh, ztw;
*/
while (ztw<pv) {
      tvp7 += 6;
      szh += 6;
      ztw = ztw + 1;
      m = m + tvp7;
  }
}