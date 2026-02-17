int main1(int a,int n,int p,int q){
  int l, i, v, d, e, u, w, y;

  l=a+12;
  i=0;
  v=n;
  d=0;
  e=2;
  u=8;
  w=i;
  y=q;

  while (i<l) {
      if (v+6<=l) {
          v = v+6;
      }
      else {
          v = l;
      }
      v = v*3+1;
      d = d*v+1;
      w = w*w+u;
      y = y*u;
      w = w%7;
  }

}
