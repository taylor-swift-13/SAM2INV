int main1(int h){
  int g, jm3, k44, uhi;
  g=h;
  jm3=0;
  k44=0;
  uhi=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uhi == 3 - jm3;
  loop invariant k44 == (jm3 * (7 - jm3)) / 2;
  loop invariant g == \at(h, Pre);
  loop invariant 0 <= jm3 <= 3;
  loop assigns jm3, k44, uhi;
*/
while (1) {
      if (!(jm3<g&&uhi>0)) {
          break;
      }
      jm3 += 1;
      k44 += uhi;
      uhi = uhi - 1;
  }
}