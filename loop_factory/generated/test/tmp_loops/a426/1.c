int main1(int m,int p){
  int l, i, v;

  l=m;
  i=0;
  v=l;

  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+4;
  }

  while (i>0) {
      l = l+i;
      i = i-1;
  }

}
