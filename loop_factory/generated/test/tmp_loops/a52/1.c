int main1(int k,int n){
  int l, i, v;

  l=n-3;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (v>0) {
      v = v-1;
  }

}
