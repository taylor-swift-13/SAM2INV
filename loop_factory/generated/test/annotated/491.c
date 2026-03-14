int main1(int o,int k){
  int q7, cj, t0, u, o0k, hk;
  q7=k*3;
  cj=1;
  t0=0;
  u=(o%28)+10;
  o0k=0;
  hk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hk == o * t0;
  loop invariant o0k == q7 * t0 + o * t0 * (t0 - 1) / 2;
  loop invariant u == ((\at(o,Pre) % 28) + 10) - ((t0 * (t0 - 1)) / 2);
  loop invariant t0 >= 0;
  loop invariant q7 == 3 * \at(k, Pre);
  loop assigns u, o0k, t0, hk;
*/
while (u>t0) {
      u -= t0;
      o0k += q7;
      t0 += 1;
      o0k = o0k + hk;
      hk = hk + o;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q7 == 3 * \at(k,Pre) - ((cj - 1) * cj) / 2;
  loop invariant cj >= 1;
  loop invariant k >= \at(k, Pre);
  loop assigns q7, cj, k, o;
*/
while (q7>cj) {
      q7 = q7 - cj;
      cj++;
      k = k+(q7%7);
      o = o+(cj%8);
      o = o*o+o;
  }
}