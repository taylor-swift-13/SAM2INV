int main1(){
  int h, yh, u2, c7sn, f1;
  h=9;
  yh=3;
  u2=0;
  c7sn=-5;
  f1=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 9;
  loop invariant 0 <= u2 <= h;
  loop invariant f1 == h + u2*(u2 + 1)/2;
  loop invariant c7sn <= u2;
  loop assigns f1, u2, c7sn;
*/
while (u2<h) {
      c7sn = u2;
      u2 += 1;
      f1 = f1 + u2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 9;
  loop invariant yh >= 3;
  loop invariant f1 == 54;
  loop invariant yh <= f1;
  loop assigns yh, c7sn;
*/
while (yh<=f1-1) {
      yh = yh + 1;
      c7sn++;
      if ((h%6)==0) {
          c7sn += 6;
      }
  }
}