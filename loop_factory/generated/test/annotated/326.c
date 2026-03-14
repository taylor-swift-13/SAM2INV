int main1(int m){
  int kv, d02, jq, nb, rh, c9lc;
  kv=100;
  d02=0;
  jq=1;
  nb=-3;
  rh=0;
  c9lc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c9lc == ((nb + 3) * (nb - 2)) / 2;
  loop invariant rh == 3 * (nb + 3);
  loop invariant jq == 1 + (nb + 3) * m;
  loop invariant nb <= kv;
  loop invariant kv == 100;
  loop assigns c9lc, nb, jq, rh;
*/
while (nb<kv) {
      rh = rh + 3;
      nb++;
      jq = jq + m;
      c9lc += nb;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c9lc - m * rh) == (5047 - m * 309);
  loop invariant (kv - c9lc) == -4947;
  loop assigns c9lc, kv, rh;
*/
while (rh<=jq-1) {
      c9lc = c9lc + m;
      kv += d02;
      rh += 1;
      kv = kv + m;
  }
}