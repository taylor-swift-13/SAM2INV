int main1(int c){
  int b3, nw5, yix, dv, hr;
  b3=15;
  nw5=b3;
  yix=0;
  dv=(c%28)+10;
  hr=b3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre);
  loop invariant dv == ((\at(c, Pre) % 28) + 10) - (yix * (yix - 1)) / 2;
  loop invariant yix >= 0;
  loop invariant b3 == 15;
  loop invariant nw5 == 15;
  loop assigns dv, c, hr, yix;
*/
while (dv>yix) {
      dv -= yix;
      c = c+b3-nw5;
      hr = hr*4+3;
      yix++;
  }
}