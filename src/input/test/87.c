int main87(int b,int k,int p){
  int r, t, a;

  r=30;
  t=0;
  a=1;

  while (t+2<=r) {
      if (a==1) {
          a = 2;
      }
      else {
          if (a==2) {
              a = 1;
          }
      }
      if (t+2<=a+r) {
          a = a*a;
      }
  }

}
