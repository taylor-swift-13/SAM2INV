int main135(int a,int k,int q){
  int u, w, d, n;

  u=k+16;
  w=u;
  d=w;
  n=w;

  while (w>=1) {
      if (d+6<=u) {
          d = d+6;
      }
      else {
          d = u;
      }
  }

  while (w+1<=u) {
      d = d+2;
      d = d*2;
      n = n+d;
  }


  /*@ assert w+1 > u; */
}
