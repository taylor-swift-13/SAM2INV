int main1(int m,int n){
  int l, i, v;

  l=(n%10)+19;
  i=0;
  v=m;

  while (i<l) {
      v = v+4;
      i = i+1;
  }

  while (v<l) {
      i = i-i;
      v = v+1;
  }

}
