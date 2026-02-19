int main1(int a,int m){
  int l, i, v;

  l=a+6;
  i=l;
  v=6;

  while (i>0) {
      v = v+v;
      v = v+1;
      i = i-1;
  }

  while (l<i) {
      v = v+1;
      l = l+1;
  }

}
