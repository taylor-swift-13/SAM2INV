int main1(){
  int z, q3;
  z=9;
  q3=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 9;
  loop invariant q3 % 3 == 0;
  loop invariant 0 <= q3 <= 9;
  loop assigns q3;
*/
while (q3-3>=0) {
      q3 = q3 - 3;
  }
}