int main1(int m,int q){
  int g, a, n;

  g=q;
  a=0;
  n=m;

  while (1) {
      n = n+3;
      if (n+7<g) {
          n = n%2;
      }
      else {
          n = n*n+n;
      }
  }

}
