int main1(int a,int p){
  int l, i, v;

  l=42;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (v<i) {
      l = l-l;
      v = v+1;
  }

}
