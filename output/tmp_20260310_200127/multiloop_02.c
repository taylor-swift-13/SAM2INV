int main1(int i){
  int dz, hdd, zux, fn5, jx9;
  dz=i+3;
  hdd=0;
  zux=0;
  fn5=5;
  jx9=hdd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dz == \at(i, Pre) + 3;
  loop invariant (zux <= dz) || (zux == 0);
  loop invariant jx9 == zux * dz - (zux * (zux - 1)) / 2;
  loop invariant (zux == 0 ==> fn5 == 5) && (zux > 0 ==> fn5 == dz - (zux - 1));
  loop invariant zux >= 0;
  loop assigns fn5, zux, jx9;
*/
while (zux<=dz-1) {
      fn5 = dz-zux;
      zux += 1;
      jx9 = jx9 + fn5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jx9 >= 0;
  loop invariant hdd >= 0;
  loop assigns hdd, jx9;
*/
while (jx9-2>=0) {
      hdd += 2;
      jx9 -= 2;
  }
/*@
  assert !(jx9-2>=0) &&
         (dz == \at(i, Pre) + 3);
*/

}