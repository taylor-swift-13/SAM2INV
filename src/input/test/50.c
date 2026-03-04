int main50(int k,int m,int q){
  int b, c, g;

  b=k+6;
  c=0;
  g=1;

  while (c<b) {
      if (g==1) {
          g = 2;
      }
      else {
          if (g==2) {
              g = 1;
          }
      }
      g = g-g;
  }

}
