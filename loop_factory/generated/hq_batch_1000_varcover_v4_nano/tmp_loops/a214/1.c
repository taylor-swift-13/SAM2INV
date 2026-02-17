int main1(int b,int k,int n,int p){
  int l, i, v, w, f, g, x, j, q;

  l=n;
  i=1;
  v=3;
  w=0;
  f=n;
  g=b;
  x=p;
  j=4;
  q=i;

  while (i<l) {
      v = v*3+5;
      w = w*v+5;
      w = w*w+q;
      x = x*2;
      g = g*g+w;
      f = f%9;
      q = q*2;
      i = i*2;
  }

}
