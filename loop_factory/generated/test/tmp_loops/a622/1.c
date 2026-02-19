int main1(int b,int m){
  int l, i, v, j;

  l=(m%33)+14;
  i=0;
  v=m;
  j=m;

  while (i<l) {
      v = v+2;
      j = j+1;
      i = i+1;
  }

  while (v<l) {
      v = v+1;
  }

}
