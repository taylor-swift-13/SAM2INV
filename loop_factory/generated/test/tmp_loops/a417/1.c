int main1(int m,int p){
  int l, i, v;

  l=(p%38)+5;
  i=0;
  v=8;

  while (i<l) {
      i = i+1;
  }

  while (v>0) {
      i = i+i;
      i = i+1;
      v = v-1;
  }

}
