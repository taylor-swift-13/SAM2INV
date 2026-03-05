int main155(int v,int s){
  int brc, dq, c1hw, p9, z99, xy;

  brc=v;
  dq=1;
  c1hw=0;
  p9=-1;
  z99=0;
  xy=v*2;

  while (dq<=brc) {
      dq = 2*dq;
      c1hw += 1;
      z99 = z99 + 3;
      p9 = p9 + dq;
      xy = xy*4+(c1hw%6)+1;
      p9 += 4;
  }

}
