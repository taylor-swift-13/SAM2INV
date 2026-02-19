int main1(int n,int p){
  int l, i, v, x;

  l=p;
  i=0;
  v=l;
  x=i;

  while (i<l) {
      v = v*4;
      x = x/4;
  }

  while (i>0) {
      l = l+3;
      v = v+1;
      i = i-1;
  }

}
