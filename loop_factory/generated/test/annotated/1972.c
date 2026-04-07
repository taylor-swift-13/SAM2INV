int main1(int n){
  int ft3, ihn9, f, ydv;
  ft3=(n%16)+20;
  ihn9=0;
  f=2;
  ydv=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 2 + ihn9;
  loop invariant ydv == -3 + (ihn9 * (ihn9 + 1)) / 2;
  loop invariant ft3 == (\at(n, Pre) % 16) + 20;
  loop invariant (0 <= ihn9 && ihn9 <= ft3);
  loop assigns f, ihn9, ydv;
*/
while (1) {
      if (ihn9>=ft3) {
          break;
      }
      f = f + 1;
      ihn9++;
      ydv += ihn9;
  }
}