int main1(){
  int s, cu, wl, ofd, d9;

  s=1*4;
  cu=0;
  wl=0;
  ofd=0;
  d9=6;

  while (wl<s&&d9>0) {
      wl += 1;
      ofd = ofd + d9;
      d9 -= 1;
      ofd += cu;
  }

}
