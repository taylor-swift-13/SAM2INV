int main99(int b,int m,int p){
  int r, v, u, t, x;

  r=b+13;
  v=0;
  u=b;
  t=m;
  x=v;

  while (u!=0&&t!=0) {
      if (u>t) {
          u = u-t;
      }
      else {
          t = t-u;
      }
  }


  /*@ assert u == 0&&t!=0; */
}
