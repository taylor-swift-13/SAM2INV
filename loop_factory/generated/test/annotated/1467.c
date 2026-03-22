int main1(int v){
  int s, q9, tl5;
  s=v;
  q9=0;
  tl5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q9 + s == \at(v, Pre);
  loop invariant tl5 == 2 * q9;
  loop invariant s == v - q9;
  loop invariant q9 >= 0;
  loop assigns q9, s, tl5;
*/
while (1) {
      if (!(q9 < s)) {
          break;
      }
      q9 += 1;
      s -= 1;
      tl5 += 2;
  }
}