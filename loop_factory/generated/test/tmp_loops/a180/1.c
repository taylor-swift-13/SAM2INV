int main1(int b,int p){
  int l, i, v;

  l=b;
  i=0;
  v=i;

  while (i<l) {
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      v = v+v;
      l = l+1;
  }

}
