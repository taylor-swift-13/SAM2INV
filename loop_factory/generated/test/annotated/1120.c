int main1(){
  int q, t, z59, ijk, ok, de;
  q=1;
  t=0;
  z59=4;
  ijk=0;
  ok=t;
  de=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z59 == 4 + ijk;
  loop invariant ok == ijk*(ijk+1)/2;
  loop invariant q == 1;
  loop invariant 0 <= ijk;
  loop invariant ijk <= q;
  loop assigns z59, ijk, ok;
*/
while (ijk<q) {
      z59++;
      ijk = ijk + 1;
      ok += ijk;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ok == ijk;
  loop invariant de >= 1;
  loop invariant q >= 1;
  loop invariant ijk <= q;
  loop invariant z59 == 4 + ijk;
  loop invariant ijk >= 1;
  loop assigns de, q, ok;
*/
while (1) {
      if (!(ok<ijk)) {
          break;
      }
      de = de+z59*ok;
      q = q+(de%5);
      ok = ijk;
  }
}