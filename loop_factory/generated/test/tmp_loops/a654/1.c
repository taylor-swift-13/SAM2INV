int main1(int a,int n){
  int l, i, v, o;

  l=(n%32)+13;
  i=l;
  v=n;
  o=n;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<o) {
      i = i+1;
      v = v+1;
  }

}
