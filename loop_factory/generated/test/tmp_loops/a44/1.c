int main1(int m,int p){
  int l, i, v;

  l=(p%26)+15;
  i=0;
  v=l;

  while (i<l) {
      v = v+v;
      v = v+8;
      i = i+1;
  }

  while (v<i) {
      l = l+v;
      v = v+1;
  }

}
