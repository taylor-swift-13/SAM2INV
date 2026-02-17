int main1(int b,int k,int n,int q){
  int l, i, v, y, m, a;

  l=(k%7)+5;
  i=l;
  v=k;
  y=q;
  m=5;
  a=k;

  while (i>0) {
      a = a*a+v;
      v = v%5;
      a = a*2;
      m = m*a;
      y = l;
      i = i-1;
  }

}
