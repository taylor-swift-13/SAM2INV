int main1(){
  int hev, b, xv;

  hev=1*3;
  b=1;
  xv=hev;

  while (1) {
      xv += b;
      if (xv+4<hev) {
          xv += b;
      }
      b += 1;
      if (b>=hev) {
          break;
      }
  }

}
