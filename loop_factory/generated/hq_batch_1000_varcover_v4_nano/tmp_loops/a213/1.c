int main1(int k,int m,int p,int q){
  int l, i, v, s, c, d;

  l=k;
  i=l;
  v=l;
  s=5;
  c=q;
  d=i;

  while (i>0) {
      v = v*2;
      s = s+v;
      c = c%8;
      if (s+2<l) {
          d = d*2;
      }
      i = i-1;
  }

}
