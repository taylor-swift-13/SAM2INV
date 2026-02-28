int main1(int k,int q){
  int n, d, v, x;

  n=q+18;
  d=0;
  v=n;
  x=n;

  while (1) {
      if (d>=n) {
          break;
      }
      v = v+1;
      d = d+1;
      v = v+1;
      x = x-1;
      x = x+v;
  }

}
