int main132(int y,int r,int x){
  int urj, w2, gfy, hc, a, g0m0;

  urj=x+9;
  w2=0;
  gfy=36;
  hc=1;
  a=0;
  g0m0=x;

  while (gfy>0&&hc<=urj) {
      if (gfy>hc) {
          gfy = gfy - hc;
      }
      else {
          gfy = 0;
      }
      hc += 1;
      a++;
      g0m0 = g0m0 + urj;
      w2++;
  }

}
