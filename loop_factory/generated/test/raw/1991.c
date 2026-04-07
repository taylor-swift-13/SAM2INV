int main1(int q){
  int gpi, ls, g, vl;

  gpi=q;
  ls=0;
  g=5;
  vl=q*2;

  while (ls < gpi) {
      g = g + q;
      ls++;
      vl = vl + q;
      q = q + ls;
  }

}
