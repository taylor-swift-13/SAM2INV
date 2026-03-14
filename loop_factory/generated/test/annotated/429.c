int main1(){
  int z, z4a, k7i, vxl, z7;
  z=(1%35)+11;
  z4a=z;
  k7i=1;
  vxl=2;
  z7=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z7 == z * k7i;
  loop invariant vxl == (k7i - 1) * (k7i - 1) + 2;
  loop invariant k7i >= 1;
  loop invariant k7i <= z + 1;
  loop assigns vxl, k7i, z7;
*/
while (k7i<=z) {
      vxl = vxl+2*k7i-1;
      k7i = k7i + 1;
      z7 += z;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z4a == z;
  loop invariant z7 >= z4a;
  loop assigns z7;
*/
while (1) {
      z7 = z7 + 1;
      if (z7>=z4a) {
          break;
      }
  }
}