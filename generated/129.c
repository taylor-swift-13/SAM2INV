int main129(int f,int u){
  int eq, d, rzae, i, gr, n, pg4;

  eq=63;
  d=0;
  rzae=0;
  i=0;
  gr=2;
  n=6;
  pg4=5;

  while (i<=eq-1) {
      i = i + 1;
      rzae += 1;
      gr++;
      n = n*4+(i%3)+1;
      d = d+rzae*rzae;
      pg4 = pg4*2+(i%5)+2;
  }

}
