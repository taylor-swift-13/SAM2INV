int main1(){
  int u8h, reb, kbh;

  u8h=0;
  reb=(1%28)+10;
  kbh=0;

  while (1) {
      if (!(reb>u8h)) {
          break;
      }
      reb = reb - u8h;
      kbh = kbh+(reb%6);
      u8h++;
      kbh = kbh*kbh+kbh;
  }

}
