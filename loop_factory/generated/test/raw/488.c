int main1(){
  int bdm, uo, u, sxtg, c;

  bdm=0;
  uo=0;
  u=(1%28)+10;
  sxtg=bdm;
  c=0;

  while (u>uo) {
      u -= uo;
      sxtg = (bdm)+(sxtg);
      uo = uo + 1;
  }

  while (sxtg>c) {
      sxtg = sxtg - c;
      c = (1)+(c);
      bdm = bdm + c;
  }

}
