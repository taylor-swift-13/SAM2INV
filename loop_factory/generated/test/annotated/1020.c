int main1(){
  int ktb, wy, p0, oa, pct;
  ktb=50;
  wy=0;
  p0=wy;
  oa=2;
  pct=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p0 == 2*wy;
  loop invariant oa == 2 + wy*(wy-1)/2;
  loop invariant pct == 7 + wy;
  loop invariant wy <= ktb;
  loop invariant 0 <= wy;
  loop assigns pct, p0, oa, wy;
*/
for (; wy+1<=ktb; wy = wy + 1) {
      pct = pct + 1;
      p0 += 2;
      oa += wy;
  }
}