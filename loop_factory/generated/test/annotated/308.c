int main1(int y){
  int e7e, cm, mt, g, mz;
  e7e=57;
  cm=e7e;
  mt=1;
  g=0;
  mz=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == (mt - 1) * (mt - 1);
  loop invariant mz == -6 + ((mt - 1) * (mt + 2)) / 2;
  loop invariant y == \at(y, Pre);
  loop invariant e7e == 57;
  loop invariant 1 <= mt <= e7e + 1;
  loop assigns g, mt, mz;
*/
while (mt<=e7e) {
      g = g+2*mt-1;
      mt = mt + 1;
      mz = mz + mt;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(y, Pre) + (mt*(mt+1))/2 - ((e7e+1)*(e7e+2))/2;
  loop invariant mt <= mz;
  loop invariant mz == 1704;
  loop invariant mt >= 58;
  loop invariant e7e == 57;
  loop assigns y, mt, cm;
*/
while (mt<mz) {
      mt = mt + 1;
      cm = mz-mt;
      y = y + mt;
  }
}