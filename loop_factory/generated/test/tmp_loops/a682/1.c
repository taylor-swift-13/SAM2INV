int main1(int a,int b){
  int l, i, v;

  l=b;
  i=l;
  v=-5;

  while (i>0) {
      v = v+1;
      i = i/2;
  }

  while (l<i) {
      v = v+3;
      v = v+l;
      l = l+1;
  }

}
