int main1(int d){
  int sh6r, eam, g1j;

  sh6r=d+16;
  eam=sh6r;
  g1j=1;

  while (eam<sh6r) {
      if (g1j>=10) {
          g1j = -1;
      }
      if (g1j<=3) {
          g1j = 1;
      }
      g1j += g1j;
      eam++;
      d = d + eam;
  }

}
