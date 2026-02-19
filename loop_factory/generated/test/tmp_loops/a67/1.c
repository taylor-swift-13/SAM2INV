int main1(int a,int b){
  int l, i, v;

  l=b;
  i=0;
  v=b;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v<l) {
      i = i+5;
      i = i+1;
      v = v*2;
  }

}
