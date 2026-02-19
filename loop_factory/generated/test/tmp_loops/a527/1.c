int main1(int k,int p){
  int l, i, v;

  l=59;
  i=0;
  v=k;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (i<v) {
      l = l-l;
      l = l+1;
      i = i+1;
  }

}
