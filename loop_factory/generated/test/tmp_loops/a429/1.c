int main1(int b,int k){
  int l, i, v, s;

  l=b+23;
  i=0;
  v=i;
  s=b;

  while (i<l) {
      v = v+1;
      s = s-1;
      s = s+s;
  }

  while (s<v) {
      l = l+1;
      i = i-1;
      s = s+5;
  }

}
