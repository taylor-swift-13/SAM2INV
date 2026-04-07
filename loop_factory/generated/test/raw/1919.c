int main1(){
  int n, emw, apr, u8, lc9, k, psi, jd0, atk6;

  n=62;
  emw=1;
  apr=7;
  u8=0;
  lc9=0;
  k=5;
  psi=0;
  jd0=-2;
  atk6=emw;

  while (emw<n) {
      if (!(!(emw%2==0))) {
          if (apr>0) {
              apr = apr - 1;
              u8 += 1;
          }
      }
      else {
          if (u8>0) {
              u8 = u8 - 1;
              apr += 1;
          }
      }
      psi = psi + u8;
      emw += 1;
      jd0 = jd0 + apr;
      lc9 = lc9 + apr;
      lc9 = lc9 + 3;
      atk6 = atk6+(emw%2);
      k += lc9;
  }

}
