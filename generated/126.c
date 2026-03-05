int main126(int u,int x,int b){
  int nhj, jkcs, p, ml;

  nhj=(u%8)+13;
  jkcs=0;
  p=4;
  ml=10;

  while (1) {
      if (!(jkcs<nhj)) {
          break;
      }
      ml += 6;
      jkcs++;
      p += 6;
      x = x + 3;
      u = u + 1;
      b = (b+p)%9;
  }

}
