int main1(int a,int m,int p,int q){
  int n, h, v, x, r, d;

  n=53;
  h=0;
  v=h;
  x=-2;
  r=h;
  d=h;

  while (1) {
      v = v*2;
      x = x+v;
      r = r%2;
      if (v+4<n) {
          d = v*v;
      }
      h = h+1;
  }

}
