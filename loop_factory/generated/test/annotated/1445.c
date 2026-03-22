int main1(){
  int ads, z, ld7, o;
  ads=1;
  z=0;
  ld7=0;
  o=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 8 - z;
  loop invariant ld7 == z * (17 - z) / 2;
  loop invariant ads == 1;
  loop invariant z >= 0;
  loop invariant o >= 0;
  loop invariant z <= ads;
  loop assigns z, ld7, o;
*/
while (z<ads&&o>0) {
      z += 1;
      ld7 = ld7 + o;
      o--;
  }
}