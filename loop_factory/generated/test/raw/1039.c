int main1(int f,int u){
  int i, d1, m7, ywh, h;

  i=u-5;
  d1=0;
  m7=0;
  ywh=0;
  h=2;

  while (1) {
      if (!(m7<i)) {
          break;
      }
      ywh += m7;
      m7 += 1;
      f += ywh;
  }

  while (1) {
      if (!(d1<m7)) {
          break;
      }
      h = m7-d1;
      u += h;
      d1 += 1;
  }

}
