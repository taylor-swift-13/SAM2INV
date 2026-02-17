int main1(int a,int m,int n,int q){
  int l, i, v, d, x, f;

  l=(n%29)+10;
  i=l;
  v=i;
  d=m;
  x=q;
  f=2;

  while (v!=0&&d!=0) {
      if (v>d) {
          v = v-d;
      }
      else {
          d = d-v;
      }
      v = v*4+3;
      d = d*v+3;
      f = f*f+x;
      d = d*2;
      x = x*x+f;
      f = v*v;
  }

}
