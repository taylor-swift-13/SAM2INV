int main1(int b,int n){
  int l, i, v, c;

  l=(n%15)+8;
  i=l;
  v=b;
  c=b;

  while (i>0) {
      v = v+1;
      c = c-1;
      i = i-1;
  }

  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

}
