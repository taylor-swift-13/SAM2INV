int main96(int b,int k,int p){
  int l, v, n;

  l=(k%28)+11;
  v=l;
  n=1;

  while (v-1>=0) {
      if (n==1) {
          n = 2;
      }
      else {
          if (n==2) {
              n = 1;
          }
      }
      n = n*n+n;
      while (1) {
          if (l==1) {
              l = 2;
          }
          else {
              if (l==2) {
                  l = 1;
              }
          }
          if (b<l+4) {
              l = l+n;
          }
      }
  }

}
