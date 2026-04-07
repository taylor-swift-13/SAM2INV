int main1(){
  int pl, xv, ox, b;

  pl=1;
  xv=0;
  ox=0;
  b=3;

  while (1) {
      if (!(xv<pl&&b>0)) {
          break;
      }
      ox += b;
      xv++;
      b = b - 1;
  }

}
