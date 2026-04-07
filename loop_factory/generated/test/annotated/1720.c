int main1(int e){
  int j9, zr8, gk, sl;
  j9=21;
  zr8=0;
  gk=0;
  sl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= zr8;
  loop invariant zr8 <= j9;
  loop invariant sl == 3 * zr8;
  loop invariant gk == (3 * zr8 * (zr8 + 1)) / 2;
  loop invariant e == \at(e, Pre) + 2 * zr8;
  loop assigns e, zr8, sl, gk;
*/
while (1) {
      if (!(zr8 < j9)) {
          break;
      }
      e += 2;
      zr8++;
      sl = sl + 3;
      gk = gk + sl;
  }
}