int main1(int j){
  int i, jop, oe;
  i=j-3;
  jop=i;
  oe=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 5*(oe + 2) == ( \at(j, Pre) - 3 - jop ) * (2 * j + 1);
  loop invariant i == (\at(j, Pre) - 3);
  loop invariant 5*(oe + 2) == ((j - 3) - jop) * (2 * j + 1);
  loop invariant jop <= j - 3;
  loop invariant jop == ((\at(j, Pre) - 3) - 5 * ((\at(j, Pre) - 3) - jop) / 5);
  loop invariant oe  == -2 + (((\at(j, Pre) - 3) - jop) / 5) * (2 * j + 1);
  loop invariant jop <= i;
  loop invariant (i - jop) % 5 == 0;
  loop invariant i == j - 3;
  loop assigns oe, jop;
*/
while (jop-5>=0) {
      oe = oe+j+j;
      oe += 1;
      jop = jop - 5;
  }
}