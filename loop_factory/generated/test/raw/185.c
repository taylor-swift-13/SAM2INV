int main1(int b,int n,int p,int q){
  int l, i, v, s;

  l=42;
  i=0;
  v=p;
  s=p;

  while (i<l) {
      v = v+2;
      s = s+v;
      s = s+s;
      v = v+s;
      if (i+2<=n+l) {
          s = s+i;
      }
      i = i+1;
  }

}
