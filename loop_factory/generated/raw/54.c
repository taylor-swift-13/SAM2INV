int main54(int k,int m,int q){
  int n, z, v;

  n=(m%14)+19;
  z=0;
  v=q;

  while (z<=n-1) {
      v = v+3;
      v = v*v;
      if (m*m<=n+5) {
          v = v*v+v;
      }
      v = v%8;
      while (1) {
          v = v+2;
      }
      while (1) {
          n = n+4;
          n = n*n+n;
      }
  }

}
