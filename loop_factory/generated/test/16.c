int main16(int a,int b,int k){
  int c, n, v, u;

  c=57;
  n=1;
  v=-2;
  u=n;

  while (1) {
      if (n<c/2) {
          v = v+u;
      }
      else {
          v = v+1;
      }
      v = v+2;
      u = u+v;
  }

}
