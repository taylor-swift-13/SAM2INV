int main1(){
  int i8a, p8, rd, mk, is, x, kx, li, t7, x0, opo;

  i8a=24;
  p8=i8a;
  rd=0;
  mk=0;
  is=0;
  x=(1%18)+5;
  kx=i8a;
  li=p8;
  t7=p8;
  x0=p8;
  opo=-1;

  while (x>=1) {
      mk = mk+1*1;
      x--;
      is = is+1*1;
      rd = rd+1*1;
      if (x0+7<i8a) {
          x0 += 4;
      }
      if (p8+3<=x0+i8a) {
          opo = opo + kx;
      }
      kx += 2;
      t7 += is;
      li--;
      kx += 1;
      if (opo+3<i8a) {
          opo += p8;
      }
  }

}
