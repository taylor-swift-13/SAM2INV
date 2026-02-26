int main79(int m,int p,int q){
  int n, k, h, j, a;

  n=m;
  k=0;
  h=q;
  j=m;
  a=m;

  while (k<n) {
      h = h+3;
      j = j+h;
      a = a+j;
      h = h+j+a;
  }

  while (a>h) {
      if (n<h) {
          k = j;
      }
      j = j+1;
      j = j*4+2;
      k = k*j+2;
  }

}
