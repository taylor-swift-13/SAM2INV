int main1(){
  int lz, c, x, xn, bl;

  lz=1+15;
  c=0;
  x=0;
  xn=-6;
  bl=0;

  while (1) {
      if (!(x<lz)) {
          break;
      }
      x = x + 1;
      xn = lz-x;
      bl += x;
  }

  while (1) {
      if (!(c<lz)) {
          break;
      }
      bl = bl + c;
      c = c + 1;
      xn = xn + c;
  }

}
