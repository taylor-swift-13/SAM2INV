int main1(int n,int p){
  int l, i, v, c;

  l=p+9;
  i=l;
  v=i;
  c=n;

  while (i>0) {
      v = v+c+c;
      i = i-1;
  }

  while (i<l) {
      i = i+3;
  }

}
