int main1(){
  int oy9, bb, ic, nac, b9v, kzs;
  oy9=(1%37)+16;
  bb=oy9+6;
  ic=0;
  nac=(1%28)+10;
  b9v=bb;
  kzs=oy9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nac == 11 - ((ic) * ((ic) - 1)) / 2;
  loop invariant ic >= 0;
  loop invariant ic <= 5;
  loop invariant kzs > 0;
  loop invariant b9v == bb*(ic + 1);
  loop assigns nac, ic, kzs, b9v;
*/
while (1) {
      if (!(nac>ic)) {
          break;
      }
      nac -= ic;
      ic = ic + 1;
      kzs = kzs+(ic%7);
      b9v += bb;
      kzs = kzs*kzs;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ic >= 0;
  loop invariant kzs > 0;
  loop invariant oy9 == 17;
  loop assigns kzs;
*/
while (1) {
      if (!(kzs<=ic-1)) {
          break;
      }
      kzs = kzs*4;
  }
}