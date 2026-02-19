int main1(int p,int q){
  int l, i, v;

  l=(q%24)+8;
  i=l;
  v=q;

  while (i>0) {
      i = i/2;
  }

  while (l<v) {
      i = i+l;
      l = l+1;
  }

}
