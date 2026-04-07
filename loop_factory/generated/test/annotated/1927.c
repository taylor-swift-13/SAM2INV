int main1(int v){
  int jo3, z, a, mnsr;
  jo3=v*5;
  z=0;
  a=0;
  mnsr=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z;
  loop invariant a == z * mnsr;
  loop invariant (mnsr == \at(v, Pre));
  loop invariant (jo3 >= 0) ==> (z <= jo3);
  loop invariant jo3 == \at(v, Pre) * 5;
  loop assigns z, a, mnsr;
*/
while (1) {
      if (!(z < jo3)) {
          break;
      }
      z += 1;
      a += mnsr;
      mnsr = mnsr+a-a;
  }
}