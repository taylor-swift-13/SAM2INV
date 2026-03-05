int main1(int g,int m){
  int dp, nv, zb;
  dp=20;
  nv=0;
  zb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m >= \at(m, Pre);
  loop invariant (m - \at(m, Pre)) % dp == 0;
  loop invariant g == \at(g, Pre);
  loop invariant (zb == 0) || (zb == dp + 1);
  loop invariant nv == 0;
  loop assigns zb, m;
*/
while (nv<=dp-1) {
      zb = dp-zb;
      zb++;
      m += dp;
  }
}