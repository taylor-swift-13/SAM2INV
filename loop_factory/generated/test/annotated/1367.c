int main1(){
  int rk9, y, vgik;
  rk9=(1%14)+14;
  y=0;
  vgik=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y;
  loop invariant y <= rk9;
  loop invariant y % 5 == 0;
  loop invariant (vgik + 1) % 13 == 0;
  loop invariant rk9 == 15;
  loop assigns vgik, y;
*/
while (y<=rk9-5) {
      vgik = vgik*2+1;
      y = y + 5;
  }
}