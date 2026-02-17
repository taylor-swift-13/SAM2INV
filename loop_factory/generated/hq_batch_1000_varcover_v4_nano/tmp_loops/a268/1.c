int main1(int a,int b,int k,int m){
  int l, i, v, c, u, x, h, o, q, j;

  l=(k%10)+7;
  i=0;
  v=l;
  c=2;
  u=-3;
  x=a;
  h=m;
  o=l;
  q=i;
  j=k;

  while (i<l) {
      x = x*x+v;
      v = v%9;
      v = q*q;
      q = q*2;
      i = i+1;
  }

}
