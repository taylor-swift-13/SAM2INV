int main1(int m,int q){
  int l, i, v;

  l=q-9;
  i=0;
  v=m;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v>0) {
      i = i+v;
      v = v-1;
  }

}
