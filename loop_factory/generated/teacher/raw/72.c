int main1(int a,int k){
  int r, g, d;

  r=(k%14)+14;
  g=0;
  d=g;

  while (g<r) {
      d = d+d;
      d = d+1;
      g = g+4;
  }

}
