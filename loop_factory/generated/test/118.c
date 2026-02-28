int main118(int a,int p,int q){
  int b, u, h, v;

  b=(p%18)+11;
  u=b;
  h=-2;
  v=u;

  while (u-1>=0) {
      h = h+4;
      h = h+u;
      v = v*v;
      v = v+h*v;
  }


  /*@ assert u-1 < 0; */
}
