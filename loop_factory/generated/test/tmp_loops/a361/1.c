int main1(int a,int m){
  int l, i, v;

  l=(m%16)+8;
  i=l;
  v=l;

  while (i>0) {
      i = i/2;
  }

  while (l<v) {
      i = i+l;
      i = i+1;
      l = l+1;
  }

}
