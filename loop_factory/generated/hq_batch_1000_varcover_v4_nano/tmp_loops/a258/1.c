int main1(int b,int m,int n,int q){
  int l, i, v, d, w, p, x, s;

  l=q+19;
  i=1;
  v=n;
  d=i;
  w=l;
  p=b;
  x=b;
  s=5;

  while (i<l) {
      if (v+1<=l) {
          v = v+1;
      }
      else {
          v = l;
      }
      v = v+i;
      d = d*d;
      w = w+v*d;
      s = s%4;
      w = w+m;
      if (d+6<l) {
          d = p*p;
      }
  }

}
