int main1(int s,int w){
  int u75, q6j3, z, zq0, y6q, w5m, ssp;
  u75=34;
  q6j3=u75;
  z=0;
  zq0=(s%28)+10;
  y6q=s;
  w5m=-4;
  ssp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y6q == \at(s,Pre) + 3*z;
  loop invariant ssp == q6j3 * z;
  loop invariant zq0 == ((\at(s,Pre) % 28) + 10) - ((z * (z - 1)) / 2);
  loop invariant z >= 0;
  loop invariant y6q == s + 3*z;
  loop assigns zq0, z, y6q, w5m, ssp;
*/
while (1) {
      if (!(zq0>z)) {
          break;
      }
      zq0 -= z;
      z += 1;
      y6q = y6q + 3;
      w5m += z;
      ssp += q6j3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u75 >= 34;
  loop assigns w5m, ssp, u75, s;
*/
while (1) {
      if (!(w5m>u75)) {
          break;
      }
      w5m = w5m - u75;
      ssp += q6j3;
      u75 = u75 + 1;
      ssp += y6q;
      s = s*s;
  }
}