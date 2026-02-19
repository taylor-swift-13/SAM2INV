int main1(int b,int m){
  int l, i, v;

  l=(b%8)+6;
  i=0;
  v=1;

  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+1;
  }

  while (i>0) {
      l = l-l;
      l = l+l;
      i = i-1;
  }

}
