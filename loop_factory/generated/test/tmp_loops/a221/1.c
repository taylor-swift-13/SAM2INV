int main1(int a,int p){
  int l, i, v, m;

  l=p-2;
  i=0;
  v=-4;
  m=4;

  while (i<l) {
      v = v+m+m;
      v = v+1;
      i = i+1;
  }

  while (v<l) {
      v = v+1;
  }

}
