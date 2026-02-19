int main1(int k,int q){
  int l, i, v;

  l=q;
  i=0;
  v=q;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v>0) {
      i = i+4;
      i = i+1;
      v = v-1;
  }

}
