int main110(int b,int k,int n){
  int g, x, s, v;

  g=b;
  x=g+6;
  s=8;
  v=k;

  while (x>0) {
      s = s*2+2;
      v = v*s+2;
      x = x/2;
  }

  while (s+1<=g) {
      v = v+4;
      v = v+1;
      while (s<g) {
          v = g-x;
          x = x+1;
      }
  }


  /*@ assert s >= g; */
}
