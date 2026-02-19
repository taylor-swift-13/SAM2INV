int main1(int b,int m){
  int l, i, v, p;

  l=m-10;
  i=l;
  v=m;
  p=8;

  while (i>0) {
      v = v+1;
      p = p+v;
      i = i-1;
  }

  while (l<i) {
      p = p+4;
      v = v+3;
      l = l+1;
  }

}
