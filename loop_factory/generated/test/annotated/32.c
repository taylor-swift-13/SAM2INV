int main1(int i){
  int r0ln, a1, t3, z;
  r0ln=i+16;
  a1=1;
  t3=-8;
  z=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r0ln == \at(i, Pre) + 16;
  loop invariant z == t3 + 12;
  loop invariant i == \at(i, Pre) + (t3 + 8) * (\at(i, Pre) + 15);
  loop invariant i - \at(i, Pre) == (r0ln - a1) * (t3 + 8);
  loop invariant t3 == z - 12;
  loop invariant i == \at(i,Pre) + (\at(i,Pre) + 15) * (z - 4);
  loop invariant z >= 4;
  loop invariant t3 >= -8;
  loop invariant z - t3 == 12;
  loop invariant i - \at(i,Pre) == (r0ln - a1) * (z - 4);
  loop invariant i == \at(i, Pre) + (z - 4) * (r0ln - 1);
  loop assigns t3, i, z;
*/
while (1) {
      if (!(t3<r0ln)) {
          break;
      }
      if (t3<r0ln) {
          t3 += 1;
      }
      i = i+r0ln-a1;
      z += 1;
  }
}