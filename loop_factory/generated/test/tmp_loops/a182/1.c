int main1(int a,int k){
  int l, i, v;

  l=(k%35)+18;
  i=l;
  v=4;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<i) {
      v = v+1;
  }

}
