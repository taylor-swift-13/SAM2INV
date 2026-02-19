int main1(int a,int k){
  int l, i, v;

  l=43;
  i=l;
  v=-6;

  while (i>0) {
      v = v+v;
      v = v+3;
      i = i-1;
  }

  while (v<i) {
      l = l+1;
      l = l-i;
      v = v+1;
  }

}
