int main1(){
  int b3y, jx, x9;
  b3y=1+15;
  jx=b3y;
  x9=jx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b3y == 1 + 15;
  loop invariant jx == b3y && (x9 == 0 || x9 == b3y);
  loop invariant jx >= 2;
  loop invariant 0 <= x9;
  loop invariant x9 <= b3y;
  loop invariant x9 == 0 || x9 == b3y;
  loop invariant jx == 16;
  loop invariant 0 <= x9 <= 16;
  loop invariant x9 == 0 || x9 == 16;
  loop invariant jx == b3y;
  loop invariant (x9 == 0) || (x9 == 1 + 15);
  loop assigns x9;
*/
while (jx>2) {
      if (jx<b3y/2) {
          x9 = x9 + x9;
      }
      else {
          x9 = x9 + 1;
      }
      x9 += jx;
      x9 = x9 - x9;
  }
}