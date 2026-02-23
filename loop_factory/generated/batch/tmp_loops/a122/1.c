int main1(int b,int m){
  int n, r, t, w;

  n=(b%8)+17;
  r=0;
  t=r;
  w=4;

  while (r<=n-5) {
      if (t+2<=n) {
          t = t+2;
      }
      else {
          t = n;
      }
  }

}
