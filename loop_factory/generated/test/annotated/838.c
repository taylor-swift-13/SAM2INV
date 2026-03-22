int main1(){
  int a4, y, dg, y2j, zs, zqt, q4;
  a4=16;
  y=-1;
  dg=a4;
  y2j=y;
  zs=y;
  zqt=(1%6)+2;
  q4=a4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a4 == 16;
  loop invariant zqt == (1 % 6) + 2;
  loop invariant zs >= -1;
  loop invariant zs <= a4;
  loop invariant y2j <= -1;
  loop invariant dg >= 16;
  loop invariant q4 >= 16;
  loop invariant dg % 3 == 1;
  loop assigns dg, zs, y2j, q4;
*/
while (1) {
      if (zs>=a4) {
          break;
      }
      dg = dg*zqt+1;
      zs = zs + 1;
      y2j = y2j*zqt;
      q4 = q4*2+(y2j%7)+0;
  }
}