int main7(int b,int k,int q){
  int h, t, l, v;

  h=(q%6)+17;
  t=0;
  l=k;
  v=t;

  while (t<=h-3) {
      l = l+v+v;
      l = l+1;
      t = t+3;
      while (v<l) {
          if (v<l/2) {
              t = t+3;
          }
          else {
              t = t-3;
          }
          v = v+1;
      }
  }

}
