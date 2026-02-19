int main1(int m,int n){
  int l, i, v;

  l=23;
  i=0;
  v=n;

  while (i<l) {
      v = v-v;
      v = v+v;
      i = i+4;
  }

  while (v<l) {
      i = i+i;
      v = v+5;
  }

}
