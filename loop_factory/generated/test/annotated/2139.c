int main1(){
  int meb, jy, cs, g99;
  meb=1+19;
  jy=meb;
  cs=-2;
  g99=meb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (meb - jy) >= 0;
  loop invariant cs <= 0;
  loop invariant meb == 1 + 19;
  loop invariant g99 + (meb - jy) * cs == meb;
  loop invariant cs <= g99;
  loop assigns cs, g99, jy;
*/
while (1) {
      if (jy>=meb) {
          break;
      }
      if (!(!(g99<=cs))) {
          cs = g99;
      }
      g99 += cs;
      jy += 1;
  }
}