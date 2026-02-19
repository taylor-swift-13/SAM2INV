int main1(int k,int m){
  int l, i, v;

  l=(k%12)+15;
  i=0;
  v=k;

  while (i<l) {
      v = v+4;
      i = i+3;
  }

  while (l>0) {
      v = v+v;
      l = l-1;
  }

}
