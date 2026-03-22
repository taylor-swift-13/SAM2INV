int main1(){
  int l, u6, kgk, r6u, n, kb, ae, t4;
  l=79;
  u6=0;
  kgk=0;
  r6u=0;
  n=0;
  kb=u6;
  ae=u6;
  t4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == u6;
  loop invariant kgk == n / 8;
  loop invariant n == kgk*8 + r6u;
  loop invariant 0 <= r6u && r6u < 8;
  loop invariant (kgk*8 + r6u) == u6;
  loop invariant 0 <= u6 && u6 <= l;
  loop invariant 0 <= kgk;
  loop invariant 0 <= kb;
  loop invariant 0 <= ae;
  loop invariant 0 <= t4;
  loop invariant n == (8*kgk + r6u);
  loop invariant kb >= u6;
  loop invariant ae >= 0 && t4 >= 0;
  loop invariant (0 <= r6u) && (r6u < 8);
  loop invariant (8 * kgk + r6u) == u6;
  loop invariant u6 == n;
  loop invariant (0 <= u6) && (u6 <= l);
  loop assigns r6u, n, kgk, u6, kb, ae, t4;
*/
while (u6<l) {
      r6u = r6u + 1;
      n += 1;
      if (r6u>=8) {
          r6u -= 8;
          kgk += 1;
      }
      u6 = u6 + 1;
      if (kb+3<l) {
          kb = kb*2;
      }
      kb = kb + u6;
      ae = ae + u6;
      ae = ae*ae;
      t4 = t4+kb*ae;
      ae = ae + kb;
  }
}