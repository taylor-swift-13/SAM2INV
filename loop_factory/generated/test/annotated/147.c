int main1(int z,int u){
  int lm0;
  lm0=(u%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(z, Pre);
  loop invariant u == \at(u, Pre);
  loop invariant lm0 >= (\at(u, Pre) % 18 + 5);
  loop invariant (z*z + u*u == 0) ==> lm0 == (\at(u, Pre) % 18 + 5) && (z*z + u*u != 0) ==> (lm0 - (\at(u, Pre) % 18 + 5)) % (z*z + u*u) == 0;
  loop invariant lm0 >= (\at(u, Pre) % 18 + 5) &&
                   ((z*z + u*u == 0) ==> lm0 == (\at(u, Pre) % 18 + 5));
  loop assigns lm0;
*/
while (lm0>0) {
      lm0 = lm0+z*z;
      lm0 = lm0+u*u;
  }
}