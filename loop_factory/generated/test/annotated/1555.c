int main1(){
  int d, n, i, zb, kzj6, d0, d9v, zdcm, f9;
  d=1*2;
  n=0;
  i=0;
  zb=0;
  kzj6=0;
  d0=0;
  d9v=0;
  zdcm=1;
  f9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= n <= d;
  loop invariant i == ((n + 2) / 3);
  loop invariant d == 2;
  loop invariant d9v == n;
  loop invariant kzj6 == zb;
  loop invariant d0 == (i*(i+1))/2;
  loop invariant f9 == ((zdcm - 1) * zdcm) / 2;
  loop invariant zb == (n + 1) / 3;
  loop invariant zdcm == 1;
  loop assigns i, d0, zb, kzj6, f9, zdcm, d9v, n;
*/
while (n < d) {
      if (n % 3 == 0) {
          i = i + 1;
          d0 = d0 + i;
      }
      if (n % 3 == 1) {
          zb++;
          kzj6 += 1;
      }
      if (n % 3 == 2) {
          f9 += zdcm;
          zdcm++;
      }
      n += 1;
      d9v += n;
      if (!(!(d9v+6<d))) {
          d9v = d9v + d9v;
      }
      else {
          d9v = d9v - d9v;
      }
      d9v = d9v + d9v;
      d9v += n;
  }
}