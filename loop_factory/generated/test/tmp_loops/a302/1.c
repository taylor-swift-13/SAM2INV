int main1(int n,int p){
  int l, i, v, y;

  l=(p%16)+16;
  i=1;
  v=l;
  y=l;

  while (i<l) {
      i = i*3;
  }

  while (v<y) {
      l = l+1;
      i = i+l;
      v = v+1;
  }

}
