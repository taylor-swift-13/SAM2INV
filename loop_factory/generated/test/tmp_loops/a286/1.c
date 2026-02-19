int main1(int m,int n){
  int l, i, v;

  l=(n%20)+15;
  i=l;
  v=i;

  while (i>0) {
      v = v+5;
      i = i-1;
  }

  while (v<l) {
      i = i-i;
      i = i+i;
      v = v+1;
  }

}
