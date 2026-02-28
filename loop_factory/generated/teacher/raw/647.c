int main1(int p,int q){
  int r, v, g, c;

  r=43;
  v=0;
  g=1;
  c=-3;

  while (1) {
      if (g+6<=r) {
          g = g+6;
      }
      else {
          g = r;
      }
      g = g+1;
      c = c+2;
      if (c+3<r) {
          g = g+v;
      }
      else {
          g = g+1;
      }
  }

}
