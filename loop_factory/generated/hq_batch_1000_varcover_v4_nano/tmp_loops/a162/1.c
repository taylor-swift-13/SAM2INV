int main1(int a,int b,int m,int n){
  int l, i, v, g, x, f, e, h, s, p;

  l=(b%10)+7;
  i=l;
  v=n;
  g=5;
  x=a;
  f=b;
  e=4;
  h=m;
  s=a;
  p=m;

  while (i>0) {
      v = v+1;
      g = g+1;
      x = x+1;
      f = v+g+x;
      v = v+i;
      g = g*g;
  }

}
