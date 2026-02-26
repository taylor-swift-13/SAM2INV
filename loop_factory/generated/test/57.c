int main57(int k,int n,int q){
  int z, x, v, u, l;

  z=n;
  x=1;
  v=0;
  u=0;
  l=0;

  while (x<z) {
      u = z-v;
      v = v+1;
      v = v+u;
  }

  while (u>=1) {
      if (v<x) {
          z = l;
      }
      l = l+1;
  }

  while (l+5<=x) {
      z = z+6;
      u = u+6;
      z = z+l;
      u = u*u;
      u = u+z*u;
  }

}
