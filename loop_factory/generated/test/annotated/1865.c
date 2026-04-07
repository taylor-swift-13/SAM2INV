int main1(int n,int m){
  int zup, zq, lva, gvn, d29, g0, u, w;
  zup=166;
  zq=1;
  lva=0;
  gvn=1;
  d29=0;
  g0=0;
  u=zup;
  w=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= lva <= 2;
  loop invariant (m - \at(m,Pre)) % 8 == 0;
  loop invariant m + 8*w == \at(m,Pre) + 24;
  loop invariant (lva == 0);
  loop invariant (d29 == 0);
  loop invariant (g0 == 0);
  loop invariant ((u - zup) % 2 == 0);
  loop invariant (zup == 166);
  loop invariant (zq == 1);
  loop invariant 0 <= d29 <= gvn;
  loop invariant w <= 3;
  loop invariant u >= zup;
  loop invariant gvn == 1;
  loop invariant gvn < zup;
  loop assigns g0, d29, gvn, lva, m, u, w;
*/
while (1) {
      if (!(lva>=0&&lva<3)) {
          break;
      }
      if (lva==0&&gvn>=zup) {
          lva = 3;
      }
      else {
          if (lva==1&&d29<gvn) {
              g0 = g0+gvn-d29;
              d29 = d29 + 1;
          }
          else {
              if (lva==1&&d29>=gvn) {
                  lva = 2;
              }
              else {
                  if (lva==2) {
                      gvn++;
                      lva = 0;
                  }
              }
          }
      }
      u = u+(zq%2);
      m++;
      m++;
      u = u + 1;
      w = w - 1;
      m += 6;
  }
}