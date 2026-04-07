int main1(int n,int g){
  int v, fy8, w0, tp, jx5, h, hc, dm, cd, eu5;
  v=13;
  fy8=0;
  w0=0;
  tp=0;
  jx5=0;
  h=0;
  hc=0;
  dm=0;
  cd=0;
  eu5=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eu5 == w0 + 2;
  loop invariant dm == w0;
  loop invariant 0 <= w0;
  loop invariant w0 <= v;
  loop invariant 0 <= jx5 <= w0;
  loop invariant 0 <= h <= w0;
  loop invariant 0 <= hc <= w0;
  loop invariant 0 <= cd;
  loop invariant cd <= 7 * w0;
  loop invariant g == \at(g,Pre);
  loop invariant fy8 == 0;
  loop invariant n >= \at(n,Pre);
  loop assigns jx5, h, hc, tp, w0, eu5, cd, n, dm;
*/
while (w0<v) {
      if (!(!(w0%8==0))) {
          if (w0%7==0) {
              jx5 = jx5 + 1;
          }
          else {
              if (w0%2==0) {
                  h += 1;
              }
              else {
                  if (1) {
                      hc += 1;
                  }
              }
          }
      }
      else {
          tp = tp + 1;
      }
      w0 += 1;
      eu5 += 2;
      cd = cd+w0%8;
      n = n + cd;
      dm += 1;
      eu5 -= 1;
      eu5 = eu5 + fy8;
  }
}