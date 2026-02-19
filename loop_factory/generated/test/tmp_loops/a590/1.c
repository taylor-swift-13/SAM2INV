int main1(int p,int q){
  int l, i, v, y;

  l=q+18;
  i=l;
  v=i;
  y=l;

  while (i>0) {
      v = v+1;
      y = y+1;
      v = v+y+y;
  }

  while (i>0) {
      v = v+1;
      l = l-1;
      i = i/2;
  }

}
