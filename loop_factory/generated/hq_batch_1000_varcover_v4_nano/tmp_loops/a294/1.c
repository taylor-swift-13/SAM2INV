int main1(int a,int b,int m,int n){
  int l, i, v, e, p, y;

  l=a+25;
  i=0;
  v=i;
  e=-8;
  p=i;
  y=b;

  while (i<l) {
      v = v+1;
      e = e+1;
      p = p+1;
      y = v+e+p;
      v = v+e;
      e = e+p;
  }

}
