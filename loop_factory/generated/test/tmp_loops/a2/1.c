int main1(int n,int p){
  int l, i, v;

  l=p;
  i=0;
  v=1;

  while (i<l) {
      v = v+6;
      v = v+i;
      i = i+1;
  }

  while (i>0) {
      v = v+1;
      i = i-1;
  }

}
