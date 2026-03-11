int main1(int t,int d){
  int vw, u, sw, m, mrq;

  vw=143;
  u=-4;
  sw=0;
  m=0;
  mrq=0;

  while (sw<vw) {
      m += sw;
      d = d + u;
      sw = sw + 1;
  }

  while (1) {
      u = u + 1;
      if (u>=mrq) {
          break;
      }
  }

}
