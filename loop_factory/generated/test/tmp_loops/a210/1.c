int main1(int p,int q){
  int l, i, v;

  l=p;
  i=0;
  v=p;

  while (i<l) {
      v = v+i;
      v = v+1;
      i = i+1;
  }

  while (l>0) {
      v = v+v;
      v = v+1;
      l = l-1;
  }

}
