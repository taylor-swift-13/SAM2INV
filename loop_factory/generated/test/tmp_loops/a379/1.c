int main1(int b,int p){
  int l, i, v, e;

  l=p+4;
  i=0;
  v=i;
  e=b;

  while (i<l) {
      v = v+3;
      e = e+3;
      i = i+2;
  }

  while (v<i) {
      l = l+4;
      e = e+2;
      v = v+1;
  }

}
