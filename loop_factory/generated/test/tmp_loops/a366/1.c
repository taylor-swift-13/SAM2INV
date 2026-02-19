int main1(int m,int n){
  int l, i, v, y;

  l=n;
  i=l;
  v=l;
  y=l;

  while (i>0) {
      v = v+y+y;
      i = i/2;
  }

  while (v>0) {
      y = y*2;
      i = i/2;
  }

}
