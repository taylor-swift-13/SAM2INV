int main1(int h,int a){
  int x, kg, lef5, etez, xh;
  x=(h%18)+6;
  kg=x;
  lef5=kg;
  etez=3;
  xh=kg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == (h % 18) + 6;
  loop invariant kg <= x;
  loop invariant (a == \at(a, Pre));
  loop invariant (h == \at(h, Pre));
  loop assigns kg;
*/
for (; kg>=1; kg--) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= \at(h, Pre);
  loop invariant a <= \at(a, Pre);
  loop invariant x <= (\at(h, Pre) % 18) + 6;
  loop invariant xh >= (\at(h, Pre) % 18) + 6;
  loop assigns x, kg, a, xh, h;
*/
while (1) {
      if (!(x>xh)) {
          break;
      }
      x -= xh;
      kg = kg*2;
      a = a+etez-lef5;
      xh = (1)+(xh);
      h += kg;
  }
}