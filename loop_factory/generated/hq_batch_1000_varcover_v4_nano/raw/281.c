int main1(int a,int b,int n,int p){
  int l, i, v, e, x, s;

  l=11;
  i=0;
  v=n;
  e=a;
  x=n;
  s=l;

  while (i<l) {
      v = v*2;
      e = e/2;
      x = x*x+v;
      if (v+6<l) {
          e = e*x;
      }
      else {
          v = v*v+x;
      }
      if (v*v<=l+5) {
          e = e*e+v;
      }
      else {
          s = e*e;
      }
      i = i+1;
  }

}
