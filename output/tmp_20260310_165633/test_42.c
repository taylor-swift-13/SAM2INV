int main1(){
  int kt, nbi, wsk, y0, j;
  kt=1+14;
  nbi=0;
  wsk=0;
  y0=8;
  j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wsk == 8 * nbi;
  loop invariant y0 == 8 + nbi;
  loop invariant j == 9 * nbi * (nbi + 1) / 2 + 8 * nbi;
  loop invariant nbi >= 0;
  loop invariant nbi <= kt;
  loop assigns nbi, wsk, y0, j;
*/
while (1) {
      if (!(nbi<=kt-1)) {
          break;
      }
      nbi++;
      wsk += 8;
      j = j + wsk;
      y0++;
      j = j + y0;
  }
/*@
  assert (wsk == 8 * nbi);
*/

}