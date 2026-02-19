int main1(int a,int n){
  int l, i, v;

  l=8;
  i=0;
  v=-2;

  while (i<l) {
      v = v+2;
      i = i+1;
  }

  while (i>0) {
      v = v+i;
      v = v+1;
      i = i-1;
  }

}
