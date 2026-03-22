int main1(){
  int ui6, mnd, hzd, qq, w7s;
  ui6=(1%16)+12;
  mnd=0;
  hzd=mnd;
  qq=-2;
  w7s=mnd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hzd == 0;
  loop invariant w7s == 0;
  loop invariant qq == -2 + mnd * ui6;
  loop invariant 0 <= mnd <= ui6;
  loop assigns mnd, hzd, qq, w7s;
*/
while (mnd < ui6) {
      hzd = hzd * 2;
      qq += ui6;
      w7s = w7s / 2;
      mnd++;
  }
}