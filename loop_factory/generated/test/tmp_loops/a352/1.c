int main1(int k,int q){
  int l, i, v;

  l=k;
  i=0;
  v=-6;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+4;
  }

}
