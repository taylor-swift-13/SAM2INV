int main1(int b,int p){
  int c, k, v, y;

  c=(p%24)+17;
  k=0;
  v=k;
  y=p;

  while (k+1<=c) {
      v = v+1;
      y = y+1;
      v = v+y+y;
  }

}
