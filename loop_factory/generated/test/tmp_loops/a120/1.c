int main1(int n,int q){
  int l, i, v, a;

  l=68;
  i=l;
  v=q;
  a=-3;

  while (i>0) {
      v = v*2;
      a = a/2;
      v = v+3;
  }

  while (l<i) {
      a = a+1;
      v = v-1;
      a = a+2;
  }

}
