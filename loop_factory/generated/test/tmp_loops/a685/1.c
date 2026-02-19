int main1(int k,int p){
  int l, i, v;

  l=k-3;
  i=0;
  v=-2;

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+1;
  }

  while (v<i) {
      l = l+l;
      v = v+2;
  }

}
