int main1(int m,int n){
  int l, i, v;

  l=n-1;
  i=1;
  v=l;

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i*3;
  }

  while (v<l) {
      i = i-i;
      v = v+5;
  }

}
