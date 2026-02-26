int main64(int k,int m,int p){
  int r, u, v, a;

  r=m-5;
  u=r;
  v=0;
  a=r;

  while (1) {
      if (u>=r) {
          break;
      }
      v = v+2;
      u = u+1;
      v = v*v+v;
      v = v%8;
      if (r*r<=r+1) {
          v = v%7;
      }
  }

  while (r-4>=0) {
      a = a+3;
      a = a+u;
      u = u+u;
  }

}
