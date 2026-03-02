int main1(int k,int p){
  int f, j, n;

  f=(p%38)+15;
  j=2;
  n=1;

  while (1) {
      n = n+3;
      if (n+1<f) {
          n = n+n;
      }
      n = n-n;
  }

}
