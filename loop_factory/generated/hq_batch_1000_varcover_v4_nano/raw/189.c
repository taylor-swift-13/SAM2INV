int main1(int a,int m,int q){
  int l, i, v, c, d;

  l=62;
  i=0;
  v=a;
  c=q;
  d=m;

  while (i<l) {
      c = c+d;
      d = d+v;
      v = v+d;
      i = i+1;
  }

}
