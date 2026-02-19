int main1(int k,int q){
  int l, i, v;

  l=(k%29)+20;
  i=0;
  v=i;

  while (i<l) {
      v = v+i;
      i = i+3;
  }

  while (l<i) {
      v = v+6;
      l = l+1;
  }

}
