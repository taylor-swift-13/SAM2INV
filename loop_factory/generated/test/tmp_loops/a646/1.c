int main1(int a,int n){
  int l, i, v, e;

  l=(a%6)+19;
  i=0;
  v=8;
  e=n;

  while (i<l) {
      v = v+2;
      i = i+1;
  }

  while (e<i) {
      v = v+1;
      l = l-1;
  }

}
