int main1(int o){
  int zjc, x, u, qtla, m2x;

  zjc=35;
  x=0;
  u=0;
  qtla=0;
  m2x=0;

  while (u<zjc) {
      if (m2x<zjc) {
          qtla = u;
      }
      m2x = m2x+zjc-x;
      u = u + 1;
  }

  while (qtla<zjc) {
      m2x = m2x + u;
      o = o+zjc-qtla;
      qtla = zjc;
  }

}
