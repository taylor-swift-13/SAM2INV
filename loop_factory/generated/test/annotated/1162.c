int main1(int u){
  int j2y, fx29, zyt, tqz, b485, xsc;
  j2y=u+11;
  fx29=1;
  zyt=0;
  tqz=(u%28)+10;
  b485=u;
  xsc=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b485 == u + 3 * zyt;
  loop invariant xsc == u + (u + 10) * zyt;
  loop invariant zyt >= 0;
  loop invariant j2y == \at(u, Pre) + 11;
  loop invariant fx29 == 1;
  loop invariant u == \at(u, Pre);
  loop invariant tqz == (u%28) + 10 - zyt*(zyt - 1)/2;
  loop assigns tqz, b485, xsc, zyt;
*/
while (tqz>zyt) {
      tqz = tqz - zyt;
      b485 = b485 + 3;
      xsc = xsc+j2y-fx29;
      zyt = (1)+(zyt);
  }
}