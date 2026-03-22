int main1(int b,int c){
  int m, a5a, x9u, qpj, k;

  m=(c%32)+4;
  a5a=0;
  x9u=1;
  qpj=1;
  k=7;

  while (x9u<=m) {
      qpj += 2;
      a5a++;
      x9u = x9u + qpj;
      k = k+(x9u%3);
  }

}
