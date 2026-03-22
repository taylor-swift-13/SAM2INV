int main1(){
  int f5, g4h, ai0, z4;
  f5=(1%20)+1;
  g4h=(1%25)+1;
  ai0=0;
  z4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= g4h <= 2;
  loop invariant 0 <= ai0;
  loop invariant 0 <= z4;
  loop invariant (ai0 % 2) == 0;
  loop invariant f5 >= 2;
  loop invariant f5 % 2 == 0;
  loop assigns ai0, f5, g4h, z4;
*/
while (g4h!=0) {
      if (g4h%2==1) {
          ai0 = ai0 + f5;
          g4h -= 1;
      }
      else {
      }
      z4 = ((ai0%6))+(z4);
      f5 = 2*f5;
      g4h = g4h/2;
      z4 = z4*z4;
  }
}