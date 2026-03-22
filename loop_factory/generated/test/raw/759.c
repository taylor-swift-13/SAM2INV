int main1(){
  int elo, xp, g9, rwq;

  elo=(1%28)+8;
  xp=(1%22)+5;
  g9=0;
  rwq=25;

  while (1) {
      if (!(xp!=0)) {
          break;
      }
      if (xp%2==1) {
          g9 += elo;
          xp -= 1;
      }
      xp = xp/2;
      elo = 2*elo;
      rwq = (elo)+(rwq);
  }

}
