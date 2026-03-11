int main1(int f){
  int f3v, zq, y7, q5o;
  f3v=f;
  zq=0;
  y7=2;
  q5o=1;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (zq<=f3v-1) {
      if (y7>=9) {
          q5o = -1;
      }
      if (y7<=2) {
          q5o = 1;
      }
      zq++;
      y7 = y7 + q5o;
  }
/*@
  assert !(zq<=f3v-1) &&
         ((y7 - zq) % 2 == 0);
*/

}