int main1(int m,int p){
  int l, i, v, y;

  l=63;
  i=0;
  v=1;
  y=l;

  while (i<l) {
      v = v+4;
      y = y+v;
      i = i+1;
  }

  while (i<y) {
      v = v+l+l;
      v = v+1;
      i = i+3;
  }

}
