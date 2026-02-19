int main1(int a,int p){
  int l, i, v, n;

  l=a+20;
  i=l;
  v=p;
  n=p;

  while (i>0) {
      v = v+3;
      i = i-1;
  }

  while (v<n) {
      l = l+v;
      v = v+1;
  }

}
