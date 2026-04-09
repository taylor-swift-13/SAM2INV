int main1(int z){
  int npb9, to, w, u2, i8, e06;
  npb9=79;
  to=0;
  w=0;
  u2=0;
  i8=z;
  e06=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant to == 2 * u2;
  loop invariant e06 == 0;
  loop invariant i8 == z + 2 * u2;
  loop invariant w == z * u2;
  loop invariant (u2 == 0 ==> npb9 == 79) && (u2 > 0 ==> npb9 == 2 * u2 - 1);
  loop invariant u2 >= 0;
  loop invariant i8 == \at(z, Pre) + 2 * u2;
  loop invariant u2 <= 1;
  loop assigns w, i8, u2, npb9, to;
*/
while (to++ < npb9) {
      w = w - e06 + z;
      i8 += 2;
      u2 += 1;
      npb9 = to++;
  }
}