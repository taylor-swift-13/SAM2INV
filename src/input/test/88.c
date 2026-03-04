int main88(int a,int b,int q){
  int s, h, f;

  s=28;
  h=s;
  f=2;

  while (h>=1) {
      if (f==1) {
          f = 2;
      }
      else {
          if (f==2) {
              f = 1;
          }
      }
      f = f*f;
  }

}
