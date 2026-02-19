int main1(int a,int b){
  int l, i, v;

  l=b;
  i=l;
  v=a;

  while (i>0) {
      v = v+v;
      v = v+i;
      i = i-1;
  }

  while (l<v) {
      i = i-i;
      l = l+1;
  }

}
