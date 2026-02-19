int main1(int n,int q){
  int l, i, v;

  l=(n%35)+17;
  i=0;
  v=-8;

  while (i<l) {
      v = l+v;
      v = v+i;
      i = i+1;
  }

  while (l>0) {
      l = l-1;
  }

}
