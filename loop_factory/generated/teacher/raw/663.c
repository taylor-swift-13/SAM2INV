int main1(int a,int q){
  int l, k, g, v, c, n;

  l=55;
  k=0;
  g=a;
  v=6;
  c=3;
  n=k;

  while (1) {
      if (n>l) {
          break;
      }
      g = g+v;
      v = v+c;
      c = c+2;
      n = n+1;
      g = g+1;
  }

}
