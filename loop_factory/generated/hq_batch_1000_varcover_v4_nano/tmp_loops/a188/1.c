int main1(int b,int n,int p,int q){
  int l, i, v, x, s, f;

  l=b;
  i=l;
  v=n;
  x=b;
  s=i;
  f=b;

  while (i>0) {
      v = v+5;
      x = x+v;
      s = s+x;
      x = x+f;
      s = s+2;
      s = s+1;
      i = i-1;
  }

}
