int main1(int a,int n){
  int b, m, p, e;

  b=n+14;
  m=0;
  p=b;
  e=b;

  while (1) {
      if (m>=b) {
          break;
      }
      p = p+2;
      m = m+1;
      p = p*p+p;
  }

}
