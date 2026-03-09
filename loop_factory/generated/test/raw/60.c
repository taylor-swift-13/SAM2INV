int main1(int g){
  int n, qt, m, xj;

  n=g+17;
  qt=0;
  m=0;
  xj=4;

  while (qt<n&&xj>0) {
      qt++;
      m += xj;
      xj -= 1;
      g += xj;
  }

}
