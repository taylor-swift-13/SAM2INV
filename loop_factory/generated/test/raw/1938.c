int main1(int w){
  int p6, oyr, ky2, r6;

  p6=38;
  oyr=0;
  ky2=w;
  r6=6;

  while (1) {
      if (!(oyr < p6)) {
          break;
      }
      oyr++;
      r6 += p6;
      ky2 = w - oyr;
  }

}
