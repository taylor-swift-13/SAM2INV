int main48(int b,int n,int q){
  int t, j, p;

  t=q+5;
  j=0;
  p=1;

  while (j<=t-1) {
      if (p==1) {
          p = 2;
      }
      else {
          if (p==2) {
              p = 1;
          }
      }
      p = p+j;
      p = p+1;
  }

}
