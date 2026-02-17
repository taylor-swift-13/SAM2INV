int main1(int a,int b,int n){
  int l, i, v, t, k, q, o, y, s, w;

  l=64;
  i=l;
  v=n;
  t=n;
  k=i;
  q=4;
  o=l;
  y=n;
  s=-4;
  w=a;

  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      v = v*2+1;
      t = t*v+1;
  }

}
