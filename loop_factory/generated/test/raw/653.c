int main1(int y,int z){
  int t, lv2, sr, e;

  t=52;
  lv2=t;
  sr=0;
  e=lv2;

  while (sr<t) {
      e = t-sr;
      z = z + e;
      sr = sr + 3;
  }

  while (lv2<=sr-1) {
      lv2 = lv2 + 1;
      e = sr-lv2;
      y = y + e;
  }

}
