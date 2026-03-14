int main1(){
  int tsh, m, v, km, qu1, k, h;
  tsh=(1%36)+15;
  m=1;
  v=0;
  km=(1%28)+10;
  qu1=m;
  k=-5;
  h=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant km == 11 - (v * (v - 1)) / 2;
  loop invariant h == -6 + 28 * (v / 8) + (v % 8) * ((v % 8) + 1) / 2;
  loop invariant tsh == 16;
  loop invariant (2*qu1 - k) == 7;
  loop invariant qu1 == 1 + v;
  loop assigns km, v, k, qu1, h;
*/
while (km>v) {
      km -= v;
      v++;
      k += 2;
      qu1 = qu1 + 1;
      h = h+(v%8);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (h >= 0);
  loop invariant k >= -5;
  loop invariant qu1 >= 1;
  loop invariant tsh >= 16;
  loop assigns k, h, tsh, qu1;
*/
while (h>=1) {
      k = k+1*1;
      h = h - 1;
      tsh = tsh+1*1;
      qu1 = qu1+1*1;
      tsh += v;
  }
}