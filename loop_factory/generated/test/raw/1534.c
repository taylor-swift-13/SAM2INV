int main1(){
  int fd, c, qvc6, x, m0, pmo, o, bh0;

  fd=(1%25)+15;
  c=0;
  qvc6=c;
  x=fd;
  m0=c;
  pmo=c;
  o=1;
  bh0=fd;

  while (c < fd) {
      c = c + 1;
      if (!(!(c <= fd/2))) {
          qvc6 = qvc6 + 1;
          x = x + 1;
      }
      else {
          qvc6--;
          x--;
      }
      if ((c%9)==0) {
          bh0++;
      }
      o += x;
      m0 += qvc6;
      pmo += qvc6;
      pmo = pmo - 1;
      m0++;
  }

}
