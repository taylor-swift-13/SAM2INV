int main1(int k,int m){
  int l, i, v, x;

  l=k;
  i=0;
  v=6;
  x=-4;

  while (i<l) {
      x = x+x;
      x = x+v;
      i = i+3;
  }

  while (i<l) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

}
