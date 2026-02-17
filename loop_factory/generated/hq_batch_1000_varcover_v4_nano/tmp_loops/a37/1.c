int main1(int a,int b,int k,int q){
  int l, i, v, x, f, s, r, y;

  l=9;
  i=0;
  v=k;
  x=8;
  f=l;
  s=l;
  r=b;
  y=q;

  while (i<l) {
      s = s*s+v;
      v = v%5;
      if ((i%3)==0) {
          f = f*2;
      }
      else {
          y = f*f;
      }
      if (y+5<l) {
          f = f*f+s;
      }
      y = v*v;
      i = i+5;
  }

}
