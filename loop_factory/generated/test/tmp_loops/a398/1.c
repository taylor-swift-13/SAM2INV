int main1(int k,int q){
  int l, i, v, x;

  l=31;
  i=l;
  v=q;
  x=k;

  while (i>0) {
      v = v+4;
      i = i-1;
  }

  while (l<v) {
      i = i+1;
      i = i+i;
      l = l+1;
  }

}
