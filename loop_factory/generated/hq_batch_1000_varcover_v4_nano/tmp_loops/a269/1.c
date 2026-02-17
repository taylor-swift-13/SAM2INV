int main1(int a,int b,int m,int n){
  int l, i, v, p, r;

  l=54;
  i=0;
  v=a;
  p=0;
  r=b;

  while (i<l) {
      v = v+3;
      p = p+v;
      r = r+p;
      v = v+p+r;
  }

}
