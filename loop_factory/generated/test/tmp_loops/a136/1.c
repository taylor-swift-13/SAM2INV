int main1(int n,int p){
  int l, i, v, y;

  l=(n%16)+5;
  i=0;
  v=-1;
  y=i;

  while (i<l) {
      v = v+1;
      y = y+4;
      i = i+1;
  }

  while (l<y) {
      v = v+l;
      l = l+3;
  }

}
