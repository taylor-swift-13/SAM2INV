int main1(int m,int n){
  int l, i, v, e;

  l=30;
  i=0;
  v=i;
  e=3;

  while (i<l) {
      e = e+e;
      e = e+v;
      i = i+1;
  }

  while (v>0) {
      e = 8;
      v = v-1;
  }

}
