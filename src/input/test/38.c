int main38(int b,int m,int n){
  int d, p, l, g;

  d=(m%27)+20;
  p=d+5;
  l=d;
  g=p;

  while (p>d) {
      g = g+1;
      l = g*g;
      l = l*l+l;
      g = g*2;
  }

  while (1) {
      if (g==1) {
          g = 2;
      }
      else {
          if (g==2) {
              g = 1;
          }
      }
      g = g+l;
      l = l+l;
  }

}
