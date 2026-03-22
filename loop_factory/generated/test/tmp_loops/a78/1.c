int main1(int y,int r){
  int inb, a, q0, p3nc, efz, s9xx, gkr, pa;

  inb=r+21;
  a=2;
  q0=13;
  p3nc=0;
  efz=1;
  s9xx=0;
  gkr=0;
  pa=y;

  while (1) {
      if (!(q0>0&&a<inb)) {
          break;
      }
      if (q0<=efz) {
          s9xx = q0;
      }
      else {
          s9xx = efz;
      }
      q0 -= s9xx;
      efz++;
      a++;
      p3nc += s9xx;
      if ((a%3)==0) {
          gkr = gkr + pa;
      }
      y = y + a;
      r = gkr+pa+y;
      pa = y-pa;
      gkr = gkr + 1;
  }

}
