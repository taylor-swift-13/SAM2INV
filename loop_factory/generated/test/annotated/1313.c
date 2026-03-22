int main1(){
  int i2, yb, ag, lvf4;
  i2=-4;
  yb=0;
  ag=(1%28)+10;
  lvf4=i2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ag == 11 - (yb * (yb - 1)) / 2;
  loop invariant i2 == -4;
  loop invariant lvf4 <= -4;
  loop invariant yb >= 0;
  loop invariant ((lvf4 % 2) == 0);
  loop assigns ag, lvf4, yb;
*/
while (ag>yb) {
      ag = ag - yb;
      lvf4 = lvf4 + i2;
      yb = yb + 1;
      lvf4 = lvf4*2;
  }
}