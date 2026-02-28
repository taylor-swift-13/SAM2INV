int main164(int a,int m,int q){
  int x, u, e, g;

  x=a;
  u=1;
  e=-6;
  g=a;

  while (u*2<=x) {
      e = e*2;
      g = g+e;
      g = g%2;
      e = e*g;
      u = u*2;
  }

  while (u+1<=g) {
      x = x+e;
      e = e*3+4;
      x = x*e+4;
      x = x*x+e;
  }

  while (x<u) {
      e = u-g;
      g = g+1;
      g = g*2;
      e = e+g;
      e = e%6;
  }

}
