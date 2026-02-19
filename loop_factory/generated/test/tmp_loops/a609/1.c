int main1(int p,int q){
  int l, i, v;

  l=49;
  i=l;
  v=6;

  while (i>0) {
      i = i-1;
  }

  while (v<i) {
      l = l+v;
      l = l-l;
      v = v+3;
  }

}
