int main1(int v,int p){
  int t, gn, z8ez, l, ru;

  t=v+22;
  gn=0;
  z8ez=0;
  l=0;
  ru=0;

  while (1) {
      if (!(gn<t)) {
          break;
      }
      ru = ru + 1;
      l = l + 1;
      if (l>=12) {
          l = l - 12;
          z8ez += 1;
      }
      gn = gn + 1;
  }

}
