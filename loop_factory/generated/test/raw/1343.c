int main1(int n,int v){
  int pc, xy9, q9, wh;

  pc=3;
  xy9=0;
  q9=(n%28)+10;
  wh=pc;

  while (q9>xy9) {
      q9 -= xy9;
      wh = wh + pc;
      xy9++;
  }

}
