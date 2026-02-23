int main1(int b,int p){
  int r, g, d, z;

  r=(p%22)+9;
  g=0;
  d=g;
  z=-3;

  while (g+4<=r) {
      if (d+4<=r) {
          d = d+4;
      }
      else {
          d = r;
      }
      d = d+1;
  }

}
