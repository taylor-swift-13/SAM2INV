int main1(int k,int q){
  int l, i, v;

  l=(q%19)+7;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (i<l) {
      v = v+i;
      i = i+1;
  }

}
