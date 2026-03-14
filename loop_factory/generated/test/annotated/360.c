int main1(int r){
  int y5, kro, r2az, elm, z;
  y5=(r%16)+9;
  kro=0;
  r2az=0;
  elm=0;
  z=(r%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant elm == r2az;
  loop invariant r2az == kro;
  loop invariant r == \at(r, Pre) + (((\at(r, Pre) % 18) + 5) - z) * y5;
  loop invariant z <= ((\at(r, Pre) % 18) + 5);
  loop assigns elm, r2az, kro, z, r;
*/
while (1) {
      if (!(z>0)) {
          break;
      }
      elm = elm+r*r;
      r2az = r2az+r*r;
      kro = kro+r*r;
      z = z - 1;
      r += y5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y5 >= (\at(r,Pre)%16) + 9;
  loop assigns r, r2az, y5;
*/
while (r2az>y5) {
      r2az -= y5;
      y5 = y5 + 1;
      r += y5;
  }
}