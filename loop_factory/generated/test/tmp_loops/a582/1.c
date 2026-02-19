int main1(int k,int n){
  int l, i, v;

  l=k+5;
  i=l;
  v=i;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<i) {
      l = l+v;
      v = v+1;
  }

}
