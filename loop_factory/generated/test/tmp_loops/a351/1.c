int main1(int p,int q){
  int l, i, v;

  l=p+5;
  i=1;
  v=p;

  while (i<l) {
      v = v+i;
      v = v+v;
      i = i*3;
  }

  while (l<i) {
      v = v+1;
      v = v+v;
      l = l+1;
  }

}
