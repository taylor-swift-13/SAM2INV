int main1(int m,int p){
  int l, i, v;

  l=m+5;
  i=l;
  v=i;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (l>0) {
      i = i+i;
      l = l-1;
  }

}
