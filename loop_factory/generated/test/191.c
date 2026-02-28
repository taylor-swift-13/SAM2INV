int main191(int k,int m,int q){
  int f, r, g, v, u;

  f=q;
  r=1;
  g=-6;
  v=-1;
  u=3;

  while (r<=f/2) {
      v = g;
      g = g+3;
  }

  while (1) {
      v = v+4;
      v = v+r;
  }

  while (v<=r/3) {
      u = u+f;
  }


  /*@ assert v > r/3; */
}
