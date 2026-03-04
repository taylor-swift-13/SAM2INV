int main53(int b,int m,int p){
  int s, x, g;

  s=(b%16)+12;
  x=3;
  g=p;

  while (1) {
      g = g+x;
      x = x+1;
  }

  while (x>s) {
      if (g==1) {
          g = 2;
      }
      else {
          if (g==2) {
              g = 1;
          }
      }
      if (m*m<=s+6) {
          g = g%4;
      }
      else {
          g = g+g;
      }
      if (x+6<=b+s) {
          g = g*g;
      }
  }

}
