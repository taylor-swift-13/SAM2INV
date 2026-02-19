int main1(int n,int q){
  int l, i, v;

  l=(n%17)+7;
  i=l;
  v=-3;

  while (i>0) {
      v = v+1;
      v = v+i;
      i = i/2;
  }

  while (v<i) {
      l = l+1;
      v = v+2;
  }

}
