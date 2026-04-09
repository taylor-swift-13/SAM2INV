int main1(int e){
  int fc7, yg7, f, ub, b, x;
  fc7=55;
  yg7=0;
  f=yg7;
  ub=2;
  b=16;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 16 - yg7;
  loop invariant f + yg7 * e == 0;
  loop invariant x == yg7 * (fc7 + 3);
  loop invariant ub + yg7 == 2;
  loop invariant f == - yg7 * \at(e, Pre);
  loop invariant (0 <= yg7 && yg7 <= fc7);
  loop invariant (ub >= 0 && b >= 0);
  loop assigns f, ub, b, x, yg7;
*/
while (1) {
      if (!(yg7 < fc7 && ub > 0 && b > 0)) {
          break;
      }
      f = (ub--, b--, f - e);
      x += fc7;
      yg7 = yg7 + 1;
      x = x + 3;
  }
}