int main1(int k,int n){
  int l, i, v, b;

  l=50;
  i=l;
  v=3;
  b=2;

  while (i>0) {
      v = v+b+b;
      i = i-1;
  }

  while (l<i) {
      v = v+l;
      l = l+1;
  }

}
