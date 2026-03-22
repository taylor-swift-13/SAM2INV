int main1(){
  int xw, q5m, pf, u, h, c4b, k6;
  xw=1*2;
  q5m=0;
  pf=0;
  u=2;
  h=0;
  c4b=xw;
  k6=xw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q5m <= xw;
  loop invariant h == q5m;
  loop invariant u == (2 + q5m) % 9;
  loop invariant pf == (q5m + xw) / 9;
  loop invariant xw == 2;
  loop invariant c4b == 2 + q5m;
  loop invariant k6 == 2 + q5m*(q5m + 3);
  loop invariant pf >= 0;
  loop invariant pf <= q5m;
  loop assigns u, h, pf, q5m, c4b, k6;
*/
while (q5m<xw) {
      u = u + 1;
      h += 1;
      if (u>=9) {
          u = u - 9;
          pf++;
      }
      q5m += 1;
      if (c4b+3<xw) {
          c4b = c4b + 1;
      }
      c4b = c4b + 1;
      k6 += h;
      k6 = k6 + c4b;
  }
}