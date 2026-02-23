int main1(int n,int p){
  int z, g, j;

  z=(p%32)+14;
  g=1;
  j=g;

  while (g+2<=z) {
      if (j+4<z) {
          j = j+g;
      }
      else {
          j = j-j;
      }
      g = g+2;
  }

}
