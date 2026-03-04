int main47(int m,int n,int p){
  int h, t, y;

  h=p-7;
  t=2;
  y=1;

  while (t<h) {
      if (y==1) {
          y = 2;
      }
      else {
          if (y==2) {
              y = 1;
          }
      }
  }

  while (1) {
      if (t==1) {
          t = 2;
      }
      else {
          if (t==2) {
              t = 1;
          }
      }
  }

}
