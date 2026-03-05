int main1(){
  int rn2k, z;
  rn2k=1;
  z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rn2k == 1;
  loop invariant z >= 0;
  loop invariant z % 2 == 0;
  loop invariant z <= 2*rn2k + 2;
  loop assigns z;
*/
while (z<rn2k) {
      z += 2;
      if (z<=z) {
          z = z;
      }
      z += z;
  }
}