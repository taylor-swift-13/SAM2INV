int main1(int b,int n,int p,int q){
  int l, i, v, x, f, w, k, t, c, a;

  l=44;
  i=l;
  v=(n%60)+60;
  x=(n%9)+2;
  f=0;
  w=0;
  k=-8;
  t=q;
  c=-2;
  a=-4;

  while (v>x*f+w) {
      if (w==x-1) {
          w = 0;
          f = f+1;
      }
      else {
          w = w+1;
      }
      w = w*w+v;
  }

}
