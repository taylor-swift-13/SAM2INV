int main1(){
  int x8, mtv, b, yi1;
  x8=(1%24)+14;
  mtv=x8;
  b=0;
  yi1=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= mtv <= x8;
  loop invariant x8 == 15;
  loop assigns mtv;
*/
while (1) {
      if (!(mtv>0)) {
          break;
      }
      mtv -= 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mtv == 0;
  loop invariant 0 <= b <= x8;
  loop invariant -2 <= yi1 <= x8;
  loop invariant yi1 <= x8 - b + mtv;
  loop assigns b, yi1;
*/
while (b<x8) {
      b += 1;
      yi1 = x8-b;
      yi1 = yi1 + mtv;
  }
}