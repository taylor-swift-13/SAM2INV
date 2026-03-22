int main1(int m){
  int l6m, q, u9, u8, eey, ly;

  l6m=m+10;
  q=0;
  u9=1;
  u8=6;
  eey=0;
  ly=0;

  while (eey<=l6m) {
      q += u9;
      eey += 1;
      u9 = u9 + u8;
      ly = ly+(q%3);
      u8 += 6;
      m = m+u9+eey;
  }

}
