int main1(int k,int m){
  int n, d, s, r;

  n=m;
  d=0;
  s=k;
  r=k;

  while (1) {
      if (d>=n) {
          break;
      }
      s = s+1;
      d = d+1;
      s = s+r;
      r = r+r;
  }

}
