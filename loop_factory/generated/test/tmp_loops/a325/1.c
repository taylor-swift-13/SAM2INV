int main1(int k,int m){
  int l, i, v;

  l=k-5;
  i=0;
  v=-8;

  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

  while (i<v) {
      i = i+3;
  }

}
