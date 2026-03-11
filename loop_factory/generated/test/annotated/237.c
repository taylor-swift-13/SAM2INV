int main1(int l,int n){
  int vld, eqvl, em, gns, e86;
  vld=45;
  eqvl=0;
  em=0;
  gns=8;
  e86=25;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eqvl == 0;
  loop invariant 0 <= em <= vld;
  loop invariant (em == 0) ==> (gns == 8);
  loop invariant (em > 0) ==> (gns == em - 1);
  loop invariant l == \at(l,Pre) + eqvl * em;
  loop assigns gns, em, l;
*/
while (1) {
      if (!(em<=vld-1)) {
          break;
      }
      gns = em;
      em = em + 1;
      l += eqvl;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eqvl >= 0;
  loop invariant e86 >= 0;
  loop invariant vld >= 0;
  loop invariant em >= 0;
  loop assigns eqvl, vld, e86;
*/
while (e86>0) {
      eqvl = eqvl+vld*e86;
      vld += em;
      e86 = 0;
  }
}