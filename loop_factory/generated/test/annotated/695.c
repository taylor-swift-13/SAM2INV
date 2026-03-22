int main1(){
  int gy, x4g, d1, k, wv, fv, l;
  gy=74;
  x4g=0;
  d1=3;
  k=3;
  wv=0;
  fv=3;
  l=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == x4g;
  loop invariant 0 <= d1 <= fv;
  loop invariant 0 <= wv <= l;
  loop invariant 3 <= k <= l + 3;
  loop invariant 0 <= x4g <= gy;
  loop invariant 0 <= wv <= gy;
  loop assigns d1, wv, k, x4g, l;
*/
while (x4g<=gy-1) {
      if (!(!(x4g%3==0))) {
          if (d1>0) {
              d1 = d1 - 1;
              wv = wv + 1;
          }
      }
      else {
          if (d1<fv) {
              d1 += 1;
              k += 1;
          }
      }
      x4g += 1;
      l = l + 1;
  }
}