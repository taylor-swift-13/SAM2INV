int main1(int y){
  int s, uf, v, g6d, d;

  s=y+6;
  uf=0;
  v=0;
  g6d=-1;
  d=s;

  while (uf<s) {
      v++;
      d = d + y;
      g6d = g6d + uf;
      uf = s;
  }

}
