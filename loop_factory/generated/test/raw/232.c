int main1(int a,int k){
  int l, i, v;

  l=31;
  i=0;
  v=a;

  while (i<l) {
      v = v*v;
      v = v%8;
      i = i+5;
  }

}
