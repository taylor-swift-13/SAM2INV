int main1(int a,int b,int m,int q){
  int l, i, v, o;

  l=(b%12)+15;
  i=0;
  v=a;
  o=l;

  while (i<l) {
      v = v+5;
      o = o+4;
      o = o+1;
      v = v+i;
      i = i+1;
  }

}
