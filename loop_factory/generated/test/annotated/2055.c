int main1(int c){
  int f, iq2, agy, u, w676;
  f=c;
  iq2=0;
  agy=0;
  u=f;
  w676=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (w676 == agy);
  loop invariant (f == \at(c, Pre));
  loop invariant (iq2 == 0);
  loop invariant (u <= f);
  loop invariant c == \at(c, Pre) + iq2 * agy;
  loop invariant agy >= 0 && (agy > 0 ==> agy <= f);
  loop invariant (agy == 0 ==> u == \at(c, Pre)) && (agy > 0 ==> u == agy - 1);
  loop assigns u, agy, w676, c;
*/
while (agy<=f-1) {
      if (w676<f) {
          u = agy;
      }
      agy = agy + 1;
      w676 = w676 + 1;
      c += iq2;
  }
}