int main1(int f){
  int f3v, zq, y7, q5o;
  f3v=f;
  zq=0;
  y7=2;
  q5o=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y7 - zq) % 2 == 0;
  loop invariant (q5o == 1) || (q5o == -1);
  loop invariant 2 <= y7 <= 9;
  loop invariant f3v == \at(f, Pre);
  loop invariant f == \at(f, Pre);
  loop invariant y7 <= 2 + zq;
  loop invariant zq >= 0 && (f3v >= 0 ==> zq <= f3v);
  loop assigns q5o, zq, y7;
*/
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