int main1(int a,int b,int q){
  int l, i, v, p, h, k, u, n;

  l=(a%16)+16;
  i=0;
  v=a;
  p=b;
  h=a;
  k=8;
  u=a;
  n=1;

  while (i<l) {
      p = p+h;
      h = h+v;
      i = i+1;
  }

}
