int main1(int k,int p){
  int l, f, d, n, y, h;

  l=k+21;
  f=0;
  d=p;
  n=k;
  y=k;
  h=-2;

  while (1) {
      if (f>=l) {
          break;
      }
      d = d+1;
      f = f+1;
      d = d+n;
      n = n+y;
  }

}
