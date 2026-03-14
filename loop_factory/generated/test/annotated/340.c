int main1(){
  int wp, t8, p2i3, owya;
  wp=3;
  t8=(1%18)+5;
  p2i3=(1%15)+3;
  owya=t8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p2i3 == t8 - 2;
  loop invariant 0 <= t8 <= 6;
  loop invariant owya >= 6;
  loop invariant wp == 3;
  loop assigns owya, p2i3, t8;
*/
while (t8!=0) {
      p2i3--;
      t8 -= 1;
      owya += t8;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant owya >= 0;
  loop invariant p2i3 >= -2;
  loop assigns owya, p2i3;
*/
for (; owya<wp; owya += 2) {
      p2i3 += owya;
      p2i3 = p2i3;
  }
}