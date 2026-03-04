int main31(int b,int m,int n){
  int e, j, k;

  e=n;
  j=0;
  k=1;

  while (j+1<=e) {
      if (k==1) {
          k = 2;
      }
      else {
          if (k==2) {
              k = 1;
          }
      }
      k = k+k;
  }

}
