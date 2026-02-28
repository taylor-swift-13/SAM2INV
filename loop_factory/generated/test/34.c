int main34(int m,int n,int p){
  int k, t, g, x;

  k=69;
  t=k;
  g=4;
  x=1;

  while (t>=1) {
      x = g;
      g = g+3;
      g = g+x;
      x = x+x;
      while (g-3>=0) {
          x = x*4;
          t = t/4;
      }
      while (g<x) {
          t = k;
          k = k+1;
          k = k+t;
          t = t+t;
      }
  }


  /*@ assert g >= x; */
}
