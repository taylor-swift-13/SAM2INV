int main1(int a,int b,int k,int n){
  int l, i, v, c, u, r, g;

  l=n;
  i=l;
  v=a;
  c=l;
  u=i;
  r=i;
  g=-4;

  while (i>0) {
      if (i<l/2) {
          v = v+c;
      }
      else {
          v = v*c;
      }
      v = v*2+3;
      c = c*v+3;
      c = c*2;
  }

}
