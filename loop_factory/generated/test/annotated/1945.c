int main1(int z){
  int dhi, y6wu, lj, p, yqt;
  dhi=z*4;
  y6wu=0;
  lj=z;
  p=1;
  yqt=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (lj + p * y6wu) == z;
  loop invariant p == 1;
  loop invariant 0 <= y6wu;
  loop invariant yqt == \at(z, Pre) + (y6wu * (y6wu + 1)) / 2;
  loop invariant dhi == 4 * \at(z, Pre);
  loop invariant (lj + p*y6wu) == \at(z, Pre);
  loop invariant (dhi >= 0 ==> y6wu <= dhi);
  loop assigns lj, y6wu, yqt;
*/
while (y6wu < dhi && lj != p) {
      lj -= p;
      y6wu = y6wu + 1;
      yqt = yqt + y6wu;
  }
}