int main75(int a,int b,int k){
  int l, f, i, n, v;

  l=k;
  f=3;
  i=(k%20)+1;
  n=(k%25)+1;
  v=0;

  while (n!=0) {
      if (n%2==1) {
          v = v+i;
          n = n-1;
      }
      else {
      }
      i = 2*i;
      n = n/2;
  }

  while (l+3<=n) {
      v = v+i;
      i = i*2;
      v = v+i;
      v = v%8;
  }


  /*@ assert l+3 > n; */
}
