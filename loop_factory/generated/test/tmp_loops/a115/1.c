int main1(int a,int k){
  int l, i, v;

  l=31;
  i=0;
  v=a;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (v<l) {
      i = i-i;
      i = i+1;
      v = v+1;
  }

}
