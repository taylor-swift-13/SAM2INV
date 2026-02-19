int main1(int b,int m){
  int l, i, v;

  l=(b%26)+4;
  i=0;
  v=-3;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (l<v) {
      i = i-i;
      i = i+i;
      l = l+1;
  }

}
