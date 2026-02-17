int main1(int a,int k,int n,int q){
  int l, i, v, x, w, d, c;

  l=k-10;
  i=1;
  v=k;
  x=-5;
  w=a;
  d=n;
  c=q;

  while (i<l) {
      v = v*3;
      x = x/3;
      if (d*d<=l+2) {
          w = c*c;
      }
      d = x*x;
      c = c*c+d;
      if ((i%7)==0) {
          x = x*2;
      }
      i = i*3;
  }

}
