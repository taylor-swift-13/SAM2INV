int main1(){
  int eee, ywp, oo, va, t32s;
  eee=1*3;
  ywp=3;
  oo=0;
  va=ywp;
  t32s=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t32s == -2 + oo * ywp;
  loop invariant (oo >= eee/2) ==> va == 3 + 2*(oo - eee/2);
  loop invariant eee == 3;
  loop invariant ywp == 3;
  loop invariant ((oo == 0 || oo == 1) ==> va == 3) && (oo == 2 ==> va == 5);
  loop invariant va >= ywp;
  loop invariant va <= ywp + 2 * oo;
  loop invariant 0 <= oo <= eee;
  loop assigns t32s, oo, va;
*/
while (1) {
      if (!(oo<eee)) {
          break;
      }
      if (!(!(oo>=eee/2))) {
          va += 2;
      }
      t32s += ywp;
      oo = oo + 1;
  }
}