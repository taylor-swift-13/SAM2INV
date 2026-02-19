int main1(int m,int p){
  int l, i, v, n;

  l=p+12;
  i=l;
  v=0;
  n=6;

  while (i>0) {
      n = n+n;
      i = i-1;
  }

  while (n<i) {
      l = l+4;
      n = n+1;
  }

}
