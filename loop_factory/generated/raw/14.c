int main14(int b,int k,int n){
  int l, g, e, v, p;

  l=33;
  g=3;
  e=n;
  v=-8;
  p=5;

  while (1) {
      v = v+e;
      e = e+2;
      v = v+e;
      p = p+v;
      p = p+2;
  }

  while (v+1<=g) {
      l = l+1;
      p = p+l*l;
  }

  while (1) {
      if (e+2<=p) {
          e = e+2;
      }
      else {
          e = p;
      }
  }

}
