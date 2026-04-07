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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= emw;
  loop invariant emw <= n;
  loop invariant apr >= 0;
  loop invariant u8 >= 0;
  loop invariant psi >= 0;
  loop invariant jd0 >= -2;
  loop invariant lc9 >= 3*(emw - 1);
  loop invariant apr + u8 == 7;
  loop invariant lc9 <= 10*(emw - 1);
  loop invariant jd0 <= -2 + 7*(emw - 1);
  loop invariant psi <= 7*(emw - 1);
  loop invariant atk6 >= 1;
  loop invariant atk6 <= emw;
  loop invariant k >= 5;
  loop invariant atk6 == 1 + (emw - 1) / 2;
  loop invariant k <= 5 + 5*(emw - 1)*(emw);
  loop assigns apr, u8, psi, emw, jd0, lc9, atk6, k;
*/
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