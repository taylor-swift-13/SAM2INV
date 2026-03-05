int main1(){
  int bp, z;
  bp=1+15;
  z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z % 3 == 0;
  loop invariant 0 <= z;
  loop invariant bp == 1 + 15;
  loop invariant z <= 3 * ((bp + 2) / 3);
  loop assigns z;
*/
while (z<bp) {
      z = z + 3;
  }
}