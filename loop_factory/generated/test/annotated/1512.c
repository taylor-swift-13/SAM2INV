int main1(int m,int l){
  int n, kl5, jf1, r, exj, eh, cw4s, hlu, z;
  n=l+13;
  kl5=0;
  jf1=0;
  r=0;
  exj=0;
  eh=0;
  cw4s=0;
  hlu=0;
  z=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == n + kl5;
  loop invariant n == l + 13;
  loop invariant kl5 <= cw4s <= 4*kl5;
  loop invariant r + exj + eh + jf1 == kl5;
  loop invariant 0 <= r;
  loop invariant 0 <= exj;
  loop invariant 0 <= eh;
  loop invariant 0 <= jf1;
  loop invariant 0 <= kl5;
  loop invariant 0 <= hlu;
  loop invariant m >= \at(m, Pre);
  loop assigns r, cw4s, jf1, exj, eh, kl5, hlu, z, m;
*/
while (kl5<n) {
      if (!(!(kl5%7==0))) {
          if (kl5%6==0) {
              r = r + 1;
              cw4s += 2;
          }
          else {
              if (kl5%4==0) {
                  exj = exj + 1;
                  cw4s = cw4s + 3;
              }
              else {
                  if (1) {
                      eh++;
                      cw4s += 4;
                  }
              }
          }
      }
      else {
          jf1 += 1;
          cw4s++;
      }
      kl5++;
      hlu = hlu+kl5%7;
      z += 1;
      m = m + hlu;
  }
}