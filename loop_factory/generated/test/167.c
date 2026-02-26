int main167(int k,int m,int q){
  int g, i, n, x;

  g=(m%33)+5;
  i=0;
  n=-3;
  x=-6;

  while (i<g) {
      n = n+2;
      n = n+x+x;
      x = x+n;
      n = n+x;
  }

}
