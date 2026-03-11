int main1(int h){
  int co, u, bz9, li, vz, t5l;
  co=54;
  u=0;
  bz9=0;
  li=h+6;
  vz=0;
  t5l=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vz == 0;
  loop invariant t5l == bz9 * (bz9 + 1) / 2;
  loop invariant ((bz9 == 0) ==> (li == h + 6)) && ((bz9 != 0) ==> (li == bz9 - 1));
  loop invariant 0 <= bz9 <= co;
  loop assigns bz9, li, t5l;
*/
while (bz9+1<=co) {
      if (vz<co) {
          li = bz9;
      }
      bz9++;
      t5l = t5l + bz9;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vz >= 0;
  loop invariant li >= 0;
  loop invariant u >= 0;
  loop invariant t5l == 1485;
  loop assigns li, u, vz;
*/
while (vz>0) {
      li = li+t5l*vz;
      u = u + li;
      vz = 0;
  }
}