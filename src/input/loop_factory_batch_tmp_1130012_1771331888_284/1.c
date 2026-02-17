int main1(int b,int k,int m,int n){
  int l, i, v, t, q, d, h;

  l=m;
  i=0;
  v=4;
  t=m;
  q=l;
  d=l;
  h=3;

  while (i<l) {
      v = v+i;
      t = t*t;
      q = q+v*t;
      if (m*m<=l+5) {
          q = q*h;
      }
      i = i+3;
  }

}
