int main1(int a){
  int d8;
  d8=(a%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((\at(a, Pre) % 20 + 5) - d8) % 3 == 0;
  loop invariant d8 <= (\at(a, Pre) % 20 + 5);
  loop invariant 6*a + d8*d8 - 3*d8 == 6*\at(a, Pre) + (\at(a, Pre) % 20 + 5) * (\at(a, Pre) % 20 + 5) - 3 * (\at(a, Pre) % 20 + 5);
  loop assigns a, d8;
*/
while (d8>0) {
      if (d8>0) {
          if (d8>0) {
              d8--;
              d8--;
              d8--;
          }
      }
      a += d8;
  }
}