int main25(int a,int b,int m){
  int y, i, q;

  y=63;
  i=0;
  q=1;

  while (i<y) {
      if (q==1) {
          q = 2;
      }
      else {
          if (q==2) {
              q = 1;
          }
      }
      if (q+1<y) {
          q = q*q;
      }
      else {
          q = q+i;
      }
      q = q*q;
  }

  while (i-3>=0) {
      if (q==1) {
          q = 2;
      }
      else {
          if (q==2) {
              q = 1;
          }
      }
      if (q+1<y) {
          q = q+i;
      }
  }

}
