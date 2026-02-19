int main1(int a,int q){
  int l, i, v, b;

  l=q;
  i=0;
  v=q;
  b=a;

  while (i<l) {
      v = v+1;
      b = b+v;
      i = i+1;
  }

  while (v<i) {
      b = b+1;
      b = b+b;
      v = v+1;
  }

}
