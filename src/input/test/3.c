int main3(int b,int k,int q){
  int r, p, c;

  r=k+13;
  p=1;
  c=2;

  while (p*2<=r) {
      if (c==1) {
          c = 2;
      }
      else {
          if (c==2) {
              c = 1;
          }
      }
      if (b*b<=r+3) {
          c = c*c;
      }
      c = c*c;
  }

}
