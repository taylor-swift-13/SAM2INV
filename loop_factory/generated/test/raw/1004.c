int main1(int m,int a){
  int u8jj, lao, vj, kz, n1;

  u8jj=65;
  lao=0;
  vj=40;
  kz=1;
  n1=0;

  while (1) {
      if (!(vj>0&&kz<=u8jj)) {
          break;
      }
      if (!(vj<=kz)) {
          vj = 0;
      }
      else {
          vj = vj - kz;
      }
      lao++;
      kz++;
      n1 = n1 + 1;
  }

}
