int main1(int n,int p){
  int l, i, v, c;

  l=n;
  i=0;
  v=3;
  c=-8;

  while (i<l) {
      c = c+c;
      c = c+v;
      i = i+1;
  }

  while (c<l) {
      i = i+1;
      i = i+i;
      c = c+1;
  }

}
