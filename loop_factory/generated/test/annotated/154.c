int main1(int l,int j){
  int z8, ryx9, bl;
  z8=16;
  ryx9=z8;
  bl=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bl == \at(l, Pre) + 5 * ((z8 - ryx9) / 3);
  loop invariant 3 * (bl - l) == 5 * (16 - ryx9);
  loop invariant 3*bl + 5*ryx9 == 3*l + 5*z8;
  loop invariant ryx9 >= 0;
  loop invariant ryx9 <= 16;
  loop assigns bl, ryx9;
*/
for (; ryx9>=3; ryx9 = ryx9 - 3) {
      bl = bl + 5;
  }
}