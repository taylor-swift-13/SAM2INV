int main1(int u){
  int fke, bds, e, c, g5fb;

  fke=(u%38)+18;
  bds=2;
  e=0;
  c=(u%28)+10;
  g5fb=-5;

  while (1) {
      if (!(c>e)) {
          break;
      }
      c = c - e;
      e += 1;
      u = u+fke-bds;
      g5fb += 1;
      g5fb = (3)+(g5fb*3);
  }

  while (bds>c) {
      bds = bds - c;
      c = c + 1;
      u = (c)+(u);
  }

}
