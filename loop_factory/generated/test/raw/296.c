int main1(int a,int q){
  int l, i, v;

  l=68;
  i=l;
  v=a;

  while (i>0) {
      v = v+i;
      v = v+2;
      i = i-1;
  }

  while (l<i) {
      v = v+l;
      v = v+v;
      l = l+1;
  }

}
