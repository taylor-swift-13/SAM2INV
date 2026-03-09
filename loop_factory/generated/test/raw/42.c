int main1(){
  int kt, nbi, wsk, y0, j;

  kt=1+14;
  nbi=0;
  wsk=0;
  y0=8;
  j=0;

  while (1) {
      if (!(nbi<=kt-1)) {
          break;
      }
      nbi++;
      wsk += 8;
      j = j + wsk;
      y0++;
      j = j + y0;
  }

}
