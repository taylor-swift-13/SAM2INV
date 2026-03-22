int main1(int r,int t){
  int djr8, wmdn, xc6, cb, l2x, p, a95, k;

  djr8=(r%30)+16;
  wmdn=1;
  xc6=1;
  cb=1;
  l2x=1;
  p=1;
  a95=t;
  k=t;

  while (1) {
      if (!(l2x<=djr8)) {
          break;
      }
      xc6 = xc6*(r/l2x);
      if ((l2x/2)%2==0) {
          p = 1;
      }
      else {
          p = -1;
      }
      cb = cb+p*xc6;
      l2x += 1;
      xc6 = xc6*(r/l2x);
      if (wmdn+7<=l2x+djr8) {
          r = r*r+a95;
      }
      k = k+(l2x%4);
      a95 = a95 + k;
      k += r;
      r += 2;
  }

}
