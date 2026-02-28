int main134(int b,int m,int p){
  int n, l, v, e, u;

  n=b+10;
  l=0;
  v=6;
  e=m;
  u=-4;

  while (l<=n-1) {
      if (l<n/2) {
          v = v+e;
      }
      else {
          v = v+1;
      }
      v = v+4;
      u = u+1;
      e = e+1;
  }


  /*@ assert l > n-1; */
}
