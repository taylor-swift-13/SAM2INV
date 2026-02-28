int main192(int b,int p,int q){
  int v, k, l, u, m;

  v=q;
  k=0;
  l=q;
  u=b;
  m=6;

  while (k+4<=v) {
      u = u+1;
      l = l+u*u;
  }

  while (1) {
      l = l+2;
  }

  while (v>=v) {
      u = u*u+u;
      u = u%8;
      v = v;
  }


  /*@ assert v < v; */
}
