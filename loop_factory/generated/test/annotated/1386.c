int main1(){
  int s46, c3, z7o, qq7h, k48, z4, tb4;
  s46=1+9;
  c3=0;
  z7o=0;
  qq7h=1;
  k48=6;
  z4=0;
  tb4=c3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z4 >= 0;
  loop invariant z4 <= s46 + 1;
  loop invariant k48 == 6 + 2*z4;
  loop invariant qq7h == z4*z4 + 5*z4 + 1;
  loop invariant tb4 == z4*(z4+1)/2;
  loop invariant 3*z7o == z4*z4*z4 + 6*z4*z4 - 4*z4;
  loop assigns z7o, z4, qq7h, tb4, k48;
*/
while (z4<=s46) {
      z7o = z7o + qq7h;
      z4 = z4 + 1;
      qq7h = qq7h + k48;
      tb4 += z4;
      k48 += 2;
  }
}