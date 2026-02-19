int main1(int b,int k){
  int l, i, v;

  l=k+17;
  i=0;
  v=i;

  while (i<l) {
      v = v+1;
      v = v+v;
      i = i+2;
  }

  while (i<l) {
      v = v+4;
      v = v-v;
      i = i+1;
  }

}
