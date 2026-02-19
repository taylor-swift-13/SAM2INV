int main1(int a,int b){
  int l, i, v;

  l=a+18;
  i=l;
  v=l;

  while (i>0) {
      v = v+v;
      i = i-1;
  }

  while (i<v) {
      l = l+i;
      i = i+1;
  }

}
