int main1(){
  int dxcq, n, y, tz, mf;
  dxcq=1+16;
  n=0;
  y=(1%40)+2;
  tz=0;
  mf=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y > 0;
  loop invariant tz >= 0;
  loop invariant mf <= 0;
  loop invariant y + mf == 3;
  loop invariant dxcq == 17;
  loop assigns tz, y, mf;
*/
while (y!=tz) {
      tz = y;
      y = (y+dxcq/y)/2;
      mf = (mf+tz)+(-(y));
  }
}