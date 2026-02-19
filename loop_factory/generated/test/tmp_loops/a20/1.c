int main1(int k,int m){
  int l, i, v;

  l=68;
  i=l;
  v=k;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<i) {
      l = l+1;
      l = l-l;
      v = v+1;
  }

}
