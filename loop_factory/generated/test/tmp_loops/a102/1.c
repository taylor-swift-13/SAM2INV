int main1(int p,int q){
  int l, i, v;

  l=q-8;
  i=0;
  v=q;

  while (i<l) {
      v = v+v;
      v = v-v;
      i = i+1;
  }

  while (v<l) {
      i = i+2;
      i = i+i;
      v = v+1;
  }

}
