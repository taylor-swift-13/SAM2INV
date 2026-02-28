int main120(int a,int n,int p){
  int w, t, r, k, v;

  w=69;
  t=w+6;
  r=w;
  k=1;
  v=n;

  while (t-w>0) {
      r = r*3;
      k = k/3;
      r = r*3+5;
      k = k*r+5;
      if (r+4<w) {
          r = v+t;
      }
      while (w*2<=v) {
          k = k+t;
          t = t*4+3;
          k = k*t+3;
          k = k%7;
      }
  }


  /*@ assert w*2 > v; */
}
