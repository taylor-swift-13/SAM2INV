int main1(int v){
  int t1b, go1m, wb, u5c, j29;

  t1b=41;
  go1m=7;
  wb=go1m;
  u5c=0;
  j29=t1b;

  while (go1m+8<=t1b) {
      u5c = u5c+wb*go1m;
      wb += go1m;
      t1b = (go1m+8)-1;
  }

  while (j29>0) {
      wb = wb + j29;
      go1m = go1m+u5c*j29;
      j29 = 0;
  }

}
