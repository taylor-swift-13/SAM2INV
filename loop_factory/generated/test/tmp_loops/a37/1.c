int main1(int b,int n){
  int l, i, v;

  l=74;
  i=0;
  v=2;

  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+2;
  }

  while (i<l) {
      v = v*i;
      v = v-v;
      i = i+1;
  }

}
