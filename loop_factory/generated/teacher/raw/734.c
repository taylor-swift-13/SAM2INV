int main1(int b,int m,int n,int p){
  int r, x, s, k;

  r=52;
  x=0;
  s=m;
  k=r;

  while (1) {
      if (x<r/2) {
          s = s+k;
      }
      else {
          s = s+1;
      }
      s = s+2;
      k = k+s;
      k = k+k;
      s = s+x;
  }

}
