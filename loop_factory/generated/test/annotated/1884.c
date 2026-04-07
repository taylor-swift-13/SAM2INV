int main1(int m){
  int vl, bw, f1g, yf, k5, lf, ff, l3;
  vl=(m%18)+6;
  bw=0;
  f1g=0;
  yf=0;
  k5=0;
  lf=0;
  ff=0;
  l3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre) + f1g * (vl + bw);
  loop invariant vl == ((\at(m, Pre) % 18) + 6);
  loop invariant l3 >= f1g;
  loop invariant l3 <= 4 * f1g;
  loop invariant yf == (f1g + 5) / 6;
  loop invariant yf + k5 + lf + ff == f1g;
  loop invariant l3 == yf + 2*k5 + 3*lf + 4*ff;
  loop invariant m == \at(m,Pre) + f1g * vl;
  loop invariant 0 <= f1g;
  loop invariant 0 <= lf <= f1g;
  loop invariant 0 <= ff <= f1g;
  loop assigns f1g, m, yf, l3, k5, lf, ff;
*/
while (f1g<vl) {
      if (f1g%6==0) {
          yf++;
          l3 = l3 + 1;
      }
      else {
          if (f1g%5==0) {
              k5++;
              l3 += 2;
          }
          else {
              if (f1g%3==0) {
                  lf = lf + 1;
                  l3 = l3 + 3;
              }
              else {
                  if (1) {
                      ff = ff + 1;
                      l3 += 4;
                  }
              }
          }
      }
      f1g += 1;
      m += vl;
      m = m + bw;
  }
}