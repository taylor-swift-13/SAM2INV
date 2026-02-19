int main1(int a,int k){
  int l, i, v;

  l=(k%29)+8;
  i=l;
  v=k;

  while (i>0) {
      v = v+1;
      v = v+i;
      i = i-1;
  }

  while (v<l) {
      i = i+i;
      v = v+1;
  }

}
