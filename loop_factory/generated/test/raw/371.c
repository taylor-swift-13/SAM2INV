int main1(){
  int cgr, n, l92, x, lc2p;

  cgr=1;
  n=0;
  l92=0;
  x=0;
  lc2p=(1%18)+5;

  while (1) {
      if (!(lc2p>=1)) {
          break;
      }
      n = n+1*1;
      l92 = l92+1*1;
      x = x+1*1;
      lc2p--;
      n = n*2+2;
  }

  while (1) {
      if (!(lc2p>cgr)) {
          break;
      }
      lc2p -= cgr;
      cgr++;
      cgr = cgr*2;
      lc2p = (cgr)+(lc2p);
      lc2p = lc2p%9;
  }

}
