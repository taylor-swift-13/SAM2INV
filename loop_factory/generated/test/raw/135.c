int main1(int b,int k,int m,int p){
  int l, i, v, h, y;

  l=64;
  i=0;
  v=k;
  h=-2;
  y=m;

  while (i<l) {
      h = h+y;
      y = y+v;
      h = h+i;
      h = h+1;
      i = i+1;
  }

}
