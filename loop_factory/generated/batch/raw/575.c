int main1(int m,int n){
  int b, t, p;

  b=m;
  t=0;
  p=m;

  while (1) {
      if (t+6<=m+b) {
          p = p*p;
      }
      else {
          p = p*p+p;
      }
      t = t+1;
  }

}
