int main1(int k,int m){
  int g, u, i, x;

  g=36;
  u=0;
  i=0;
  x=0;

  while (i<g) {
      if (i<g/2) {
          x = x+2;
      }
      else {
          x = x-2;
      }
      i = i+1;
      x = x+x;
  }

}
