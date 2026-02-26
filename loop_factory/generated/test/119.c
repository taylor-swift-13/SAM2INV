int main119(int a,int b,int n){
  int t, k, v, u, e;

  t=b;
  k=2;
  v=k;
  u=n;
  e=n;

  while (1) {
      if (v+3<=t) {
          v = v+3;
      }
      else {
          v = t;
      }
      v = v*2;
  }

  while (k!=0&&v!=0) {
      if (k>v) {
          k = k-v;
      }
      else {
          v = v-k;
      }
      while (1) {
          if (u%6==4) {
              e = e+1;
          }
          else {
              t = t+1;
          }
          if (u%6==5) {
              v = v+1;
          }
          else {
          }
          e = e+u;
          t = t*t;
      }
  }

}
