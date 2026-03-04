int main67(int a,int k,int q){
  int x, h, n;

  x=a+24;
  h=x;
  n=1;

  while (h>=1) {
      if (n==1) {
          n = 2;
      }
      else {
          if (n==2) {
              n = 1;
          }
      }
      if (h+4<=a+x) {
          n = n+h;
      }
      else {
          n = n+h;
      }
      n = n+h;
  }

}
