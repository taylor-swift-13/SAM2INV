int main1(int k,int p){
  int l, i, v;

  l=(p%33)+7;
  i=l;
  v=k;

  while (i>0) {
      i = i-1;
  }

  while (l>0) {
      i = i+i;
      l = l-1;
  }

}
