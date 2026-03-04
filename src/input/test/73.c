int main73(int m,int n,int q){
  int e, k, j;

  e=43;
  k=0;
  j=1;

  while (k<=e-1) {
      if (j==1) {
          j = 2;
      }
      else {
          if (j==2) {
              j = 1;
          }
      }
      if ((k%3)==0) {
          j = j*2;
      }
      j = j*j+j;
      j = j*2;
  }

}
