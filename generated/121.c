int main121(int y,int v,int o){
  int m, mycr, kx6, z10, ps;

  m=v;
  mycr=0;
  kx6=0;
  z10=12;
  ps=o;

  while (1) {
      if (!(kx6<m)) {
          break;
      }
      ps += 1;
      mycr = mycr + y;
      kx6 += 1;
      v = v+(mycr%3);
      y = y*y+z10;
      z10 = z10%5;
  }

}
