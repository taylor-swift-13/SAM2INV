int main1(){
  int f7, lbbg, yciy, f860, l0nl;
  f7=1;
  lbbg=0;
  yciy=(1%28)+10;
  f860=0;
  l0nl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yciy + (lbbg * (lbbg - 1)) / 2 == 11;
  loop invariant yciy >= 0;
  loop invariant f860 >= 0;
  loop invariant f860 == lbbg * (f7 + l0nl);
  loop invariant f7 == 1;
  loop invariant l0nl == 0;
  loop assigns yciy, lbbg, f860;
*/
while (yciy>lbbg) {
      yciy = yciy - lbbg;
      f860 = f860 + f7;
      lbbg += 1;
      f860 += l0nl;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f7 <= 1;
  loop invariant l0nl >= 0;
  loop invariant f860 >= 0;
  loop invariant f7 >= 0;
  loop invariant yciy >= 0;
  loop assigns f7, yciy, l0nl;
*/
while (f7>yciy) {
      f7 -= yciy;
      yciy = (1)+(yciy);
      l0nl += f860;
  }
}