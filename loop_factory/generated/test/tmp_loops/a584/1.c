int main1(int b,int q){
  int l, i, v;

  l=(b%37)+8;
  i=l;
  v=b;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<i) {
      l = l-l;
      l = l+1;
      v = v+1;
  }

}
