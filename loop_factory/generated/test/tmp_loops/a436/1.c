int main1(int b,int p){
  int l, i, v;

  l=b-1;
  i=0;
  v=2;

  while (i<l) {
      v = v-v;
      v = v+3;
      i = i+1;
  }

  while (v<i) {
      l = l+v;
      v = v+1;
  }

}
