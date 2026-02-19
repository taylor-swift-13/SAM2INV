int main1(int n,int p){
  int l, i, v, c;

  l=n+5;
  i=l;
  v=-2;
  c=p;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<l) {
      i = i+3;
      c = c+i;
      v = v+4;
  }

}
