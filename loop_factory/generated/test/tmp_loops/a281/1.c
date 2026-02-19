int main1(int b,int p){
  int l, i, v;

  l=(p%29)+13;
  i=1;
  v=l;

  while (i<l) {
      v = v+i;
      i = i*2;
  }

  while (l>0) {
      i = i+1;
      i = i+i;
      l = l-1;
  }

}
