int main1(int g,int q){
  int wp, momq, rx, n4vk, yb, mt, e;

  wp=g;
  momq=1;
  rx=4;
  n4vk=momq;
  yb=0;
  mt=3;
  e=wp;

  while (1) {
      if (mt>wp) {
          break;
      }
      rx = rx + n4vk;
      n4vk = n4vk + yb;
      yb += 6;
      mt = mt + 1;
      e = e + yb;
  }

}
