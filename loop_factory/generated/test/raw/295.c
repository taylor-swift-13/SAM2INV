int main1(int k,int q){
  int l, i, v;

  l=13;
  i=l;
  v=k;

  while (i>0) {
      v = v+i;
      i = i/2;
  }

  while (l<v) {
      i = i+1;
      l = l+1;
  }

}
