int main1(int w){
  int me, u0jy, yl;

  me=0;
  u0jy=(w%28)+10;
  yl=0;

  while (u0jy>me) {
      u0jy -= me;
      yl += u0jy;
      me = me + 1;
      yl = yl*2;
  }

}
