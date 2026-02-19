int main1(int b,int q){
  int l, i, v;

  l=(b%17)+9;
  i=0;
  v=b;

  while (i<l) {
      v = v+i;
      v = v+1;
      i = i+5;
  }

  while (i<v) {
      l = l+i;
      i = i*3;
  }

}
