int main1(int k,int q){
  int l, i, v, a;

  l=q;
  i=0;
  v=k;
  a=k;

  while (i<l) {
      v = v*3;
      a = a/3;
      v = v+1;
  }

  while (v>0) {
      l = l+2;
      v = v-1;
  }

}
