int main1(){
  int u8h, reb, kbh;
  u8h=0;
  reb=(1%28)+10;
  kbh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant reb == 11 - (u8h * (u8h - 1)) / 2;
  loop invariant 0 <= u8h;
  loop invariant reb >= 0;
  loop invariant kbh >= 0;
  loop assigns kbh, reb, u8h;
*/
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