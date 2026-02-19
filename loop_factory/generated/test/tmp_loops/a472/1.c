int main1(int n,int q){
  int l, i, v;

  l=q;
  i=0;
  v=i;

  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+1;
  }

  while (i<l) {
      v = v+i;
      v = v+2;
      i = i*3;
  }

}
