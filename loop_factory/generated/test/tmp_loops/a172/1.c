int main1(int m,int q){
  int l, i, v;

  l=28;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (l>0) {
      v = v+1;
      l = l-1;
  }

}
