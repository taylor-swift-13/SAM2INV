int main51(int a,int p,int q){
  int b, u, v, r;

  b=p+13;
  u=0;
  v=p;
  r=2;

  while (1) {
      r = v;
      v = v+2;
  }

  while (r>v) {
      r = r-2;
  }


  /*@ assert r <= v; */
}
