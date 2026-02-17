int main1(int a,int k,int n,int q){
  int l, i, v, p, b, m;

  l=(k%35)+15;
  i=0;
  v=l;
  p=n;
  b=k;
  m=l;

  while (i<l) {
      v = v+p;
      p = p+b;
      i = i+4;
  }

}
