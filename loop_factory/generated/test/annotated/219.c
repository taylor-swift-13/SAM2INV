int main1(int y){
  int w, yg, zg, ye0, p6b;
  w=52;
  yg=w;
  zg=w;
  ye0=0;
  p6b=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (yg == 0) ==> (ye0 == zg);
  loop invariant (yg >= 1) ==> (ye0 == 0);
  loop invariant zg == 52;
  loop invariant w == 52;
  loop invariant y == \at(y, Pre);
  loop invariant 0 <= yg <= w;
  loop assigns ye0, yg;
*/
while (yg>=1) {
      ye0 = ye0 + zg;
      yg = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 52 + yg * y;
  loop invariant p6b == 16;
  loop invariant y == \at(y, Pre);
  loop invariant 0 <= yg <= p6b;
  loop assigns w, yg;
*/
while (1) {
      if (!(yg<=p6b-1)) {
          break;
      }
      w = w + y;
      yg += 1;
  }
}