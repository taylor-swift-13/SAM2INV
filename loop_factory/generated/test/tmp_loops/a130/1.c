int main1(int n,int p){
  int l, i, v;

  l=p;
  i=0;
  v=n;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      v = v+2;
      v = v+1;
      l = l+1;
  }

}
