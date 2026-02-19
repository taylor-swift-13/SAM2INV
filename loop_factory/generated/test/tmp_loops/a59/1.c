int main1(int a,int n){
  int l, i, v;

  l=(a%32)+17;
  i=0;
  v=i;

  while (i<l) {
      v = v+1;
      i = i+4;
  }

  while (l<v) {
      i = i+1;
      i = i+l;
      l = l+1;
  }

}
