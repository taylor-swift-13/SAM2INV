int main1(){
  int qdr, kxsc, xl, uyj;
  qdr=0;
  kxsc=0;
  xl=(1%28)+10;
  uyj=qdr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xl == 11 - (kxsc*(kxsc - 1))/2;
  loop invariant uyj == 11*kxsc - (kxsc*(kxsc - 1)*(kxsc + 1))/6;
  loop invariant xl == 11 - kxsc*(kxsc - 1)/2;
  loop invariant qdr == 0;
  loop invariant xl >= 1;
  loop invariant kxsc >= 0;
  loop invariant uyj >= 0;
  loop invariant xl + kxsc*(kxsc - 1)/2 == 11;
  loop invariant 0 <= kxsc;
  loop assigns xl, uyj, kxsc;
*/
while (xl>kxsc) {
      xl = xl - kxsc;
      uyj += xl;
      kxsc = (1)+(kxsc);
  }
}