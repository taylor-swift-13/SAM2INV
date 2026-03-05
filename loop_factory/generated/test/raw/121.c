int main1(int t){
  int gu, wji, y1, s7;

  gu=54;
  wji=3;
  y1=2;
  s7=1;

  while (wji<gu) {
      if (y1>=11) {
          s7 = -1;
      }
      if (y1<=2) {
          s7 = 1;
      }
      y1 += s7;
      wji = wji + 1;
      t += wji;
  }

}
