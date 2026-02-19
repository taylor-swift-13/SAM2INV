int main1(int n,int p){
  int l, i, v;

  l=(n%32)+13;
  i=0;
  v=n;

  while (i<l) {
      v = v+i;
      v = v+1;
      i = i+2;
  }

  while (i<l) {
      i = i+1;
  }

}
