int main1(int n,int q){
  int l, i, v;

  l=(q%6)+8;
  i=0;
  v=i;

  while (i<l) {
      v = v+2;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      v = v+1;
      l = l+1;
  }

}
