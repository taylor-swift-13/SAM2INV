int main1(int b,int k,int n,int q){
  int l, i, v, m, r, p, s;

  l=k;
  i=0;
  v=q;
  m=8;
  r=1;
  p=0;
  s=-8;

  while (i<l) {
      v = v*2;
      m = m+v;
      r = r%8;
      v = v*m;
      m = r*r;
      if ((i%8)==0) {
          s = s*2;
      }
      i = i+5;
  }

}
