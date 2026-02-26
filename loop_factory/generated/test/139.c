int main139(int b,int n,int q){
  int r, t, h, j, v;

  r=26;
  t=0;
  h=8;
  j=q;
  v=0;

  while (t<=r-3) {
      if (t<r/2) {
          h = h+j;
      }
      else {
          h = h*j;
      }
      h = h*3;
      j = j/3;
      h = v*v;
      v = v*v+h;
  }

  while (v>=v) {
      h = h+2;
      if (v+2<=t+t) {
          h = h+h;
      }
      else {
          h = h-h;
      }
  }

}
