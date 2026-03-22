int main1(){
  int k0, rw0, rr, jvs, e, h9;
  k0=1-1;
  rw0=k0+4;
  rr=0;
  jvs=0;
  e=k0;
  h9=k0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rr == jvs;
  loop invariant e == rw0 * rr;
  loop invariant jvs <= k0;
  loop invariant e == k0 + rw0 * rr;
  loop invariant (rr >= 0);
  loop invariant (e >= 0);
  loop assigns jvs, rr, e;
*/
while (1) {
      if (!(jvs<k0)) {
          break;
      }
      jvs = jvs + 1;
      rr = rr + 1;
      e = e + rw0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == k0;
  loop invariant k0 <= rr;
  loop invariant rr == 0;
  loop invariant 0 <= k0;
  loop invariant h9 == (k0 / 8) * 28 + ((k0 % 8) * ((k0 % 8) + 1)) / 2;
  loop assigns k0, e, h9;
*/
while (k0<rr) {
      k0 += 1;
      e += 1;
      h9 = h9+(k0%8);
  }
}