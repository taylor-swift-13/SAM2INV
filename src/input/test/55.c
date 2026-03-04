int main55(int k,int m,int q){
  int r, y, f;

  r=52;
  y=0;
  f=1;

  while (y+4<=r) {
      if (f==1) {
          f = 2;
      }
      else {
          if (f==2) {
              f = 1;
          }
      }
      f = f-f;
      f = f+f;
  }

}
