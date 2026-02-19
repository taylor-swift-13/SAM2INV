int main1(int p,int q){
  int l, i, v;

  l=p;
  i=0;
  v=l;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (l<v) {
      i = i+i;
      i = i+l;
      l = l+1;
  }

}
