int main1(int p,int q){
  int l, i, v, c;

  l=q;
  i=l;
  v=p;
  c=-4;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (l<v) {
      i = i+i;
      i = i+c;
      l = l+1;
  }

}
