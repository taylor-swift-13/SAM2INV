int main1(int b,int k){
  int l, i, v;

  l=(k%33)+11;
  i=l;
  v=3;

  while (i>0) {
      v = v+v;
      i = i-1;
  }

  while (v<i) {
      v = v+1;
  }

}
