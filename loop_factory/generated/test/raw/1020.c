int main1(){
  int ktb, wy, p0, oa, pct;

  ktb=50;
  wy=0;
  p0=wy;
  oa=2;
  pct=7;

  for (; wy+1<=ktb; wy = wy + 1) {
      pct = pct + 1;
      p0 += 2;
      oa += wy;
  }

}
