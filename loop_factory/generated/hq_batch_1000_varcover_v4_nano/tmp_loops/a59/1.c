int main1(int a,int m,int n,int p){
  int l, i, v, x, e, h, s, o;

  l=a;
  i=0;
  v=-1;
  x=a;
  e=5;
  h=m;
  s=a;
  o=4;

  while (i<l) {
      v = v+i;
      x = x*x;
      e = e+v*x;
      if (x+2<l) {
          v = v*e;
      }
      v = v%5;
      s = e*e;
      e = e*h;
      i = i+1;
  }

}
