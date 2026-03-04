int main59(int k,int n,int q){
  int v, t, d;

  v=n;
  t=v;
  d=t;

  while (t>0) {
      t = t-1;
      while (1) {
          if (v==1) {
              v = 2;
          }
          else {
              if (v==2) {
                  v = 1;
              }
          }
          if (v+1<d) {
              v = v*2;
          }
      }
  }

}
