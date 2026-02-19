int main1(int k,int m){
  int l, i, v;

  l=k;
  i=0;
  v=k;

  while (i<l) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

  while (i>0) {
      v = v+i;
      i = i-1;
  }

}
