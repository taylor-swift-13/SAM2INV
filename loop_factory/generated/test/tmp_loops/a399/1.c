int main1(int b,int n){
  int l, i, v;

  l=(b%10)+7;
  i=l;
  v=i;

  while (i>0) {
      v = v+1;
      v = v+v;
      i = i-1;
  }

  while (i<v) {
      l = l-l;
      i = i+3;
  }

}
