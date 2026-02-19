int main1(int n,int q){
  int l, i, v;

  l=(n%31)+5;
  i=0;
  v=0;

  while (i<l) {
      i = i+1;
  }

  while (v<l) {
      i = i+i;
      i = i-i;
      v = v+1;
  }

}
