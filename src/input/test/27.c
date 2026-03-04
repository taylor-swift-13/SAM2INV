int main27(int a,int m,int q){
  int f, j, t;

  f=(q%12)+15;
  j=f;
  t=1;

  while (j>3) {
      if (t==1) {
          t = 2;
      }
      else {
          if (t==2) {
              t = 1;
          }
      }
      t = t*t;
  }

}
