int main1(int m,int n){
  int e, y, i, k;

  e=(m%6)+15;
  y=0;
  i=-2;
  k=e;

  while (y<=e-1) {
      i = i*i+i;
      i = i%2;
      y = y+1;
  }

}
