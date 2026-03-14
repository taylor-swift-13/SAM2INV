int main1(){
  int nuo, xx, fl, mx, lx1;

  nuo=63;
  xx=0;
  fl=0;
  mx=0;
  lx1=0;

  while (1) {
      if (!(xx<nuo)) {
          break;
      }
      mx++;
      lx1++;
      if (mx>=11) {
          mx -= 11;
          fl = fl + 1;
      }
      xx = xx + 1;
  }

}
