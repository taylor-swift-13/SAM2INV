int main1(int y,int u){
  int q, u0, bfa, g7, pa;

  q=y+16;
  u0=0;
  bfa=0;
  g7=0;
  pa=0;

  for (; u0<q; u0 = u0 + 1) {
      g7 += 1;
      pa += 1;
      if (g7>=4) {
          g7 -= 4;
          bfa = bfa + 1;
      }
  }

}
