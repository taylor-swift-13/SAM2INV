int main1(int x,int k){
  int xyn, g, dod;

  xyn=52;
  g=0;
  dod=-6;

  while (1) {
      if (!(g<xyn)) {
          break;
      }
      if (dod+5<=xyn) {
          dod = dod + 5;
      }
      else {
          dod = xyn;
      }
      x += 2;
      k = k + dod;
  }

}
