int main1(int a,int n,int p,int q){
  int l, i, v, b, j, k, d;

  l=n;
  i=0;
  v=-8;
  b=q;
  j=1;
  k=l;
  d=a;

  while (i<l) {
      v = v+b;
      b = b+j;
      j = j+6;
      if (i+7<=a+l) {
          b = b*k;
      }
      k = k*j;
      i = i+5;
  }

}
