int main1(int m,int n,int q){
  int l, i, v, f, d, b;

  l=18;
  i=0;
  v=8;
  f=n;
  d=i;
  b=n;

  while (i<l) {
      b = b*b+v;
      v = v%5;
      d = b+i;
      i = i+1;
  }

}
