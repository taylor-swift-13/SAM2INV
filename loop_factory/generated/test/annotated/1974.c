int main1(int y){
  int yi, x, ifp, xj8g;
  yi=y+10;
  x=0;
  ifp=y*yi;
  xj8g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (2 * ifp + x * y) == (2 * \at(y, Pre) * (\at(y, Pre) + 10));
  loop invariant (x * y) == xj8g;
  loop invariant x >= 0;
  loop invariant (x % 2) == 0;
  loop invariant (x != 0) ==> (yi == xj8g);
  loop invariant ifp + (x/2) * y == \at(y, Pre) * (\at(y, Pre) + 10);
  loop invariant 2 * ((\at(y, Pre) * (\at(y, Pre) + 10)) - ifp) == (y * x);
  loop assigns x, xj8g, ifp, yi;
*/
while (1) {
      if (!((xj8g += y, x++ < yi))) {
          break;
      }
      ifp = ifp - y;
      yi = xj8g += y, x++;
  }
}