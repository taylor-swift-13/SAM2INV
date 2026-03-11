int main1(int o){
  int ju9, zyj, zl8, r2;

  ju9=(o%13)+12;
  zyj=0;
  zl8=1;
  r2=1;

  while (zyj<ju9) {
      if (zl8>=10) {
          r2 = -1;
      }
      if (zl8<=1) {
          r2 = 1;
      }
      zyj++;
      zl8 += r2;
  }

}
