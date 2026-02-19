int main1(int m,int p){
  int l, i, v;

  l=39;
  i=0;
  v=l;

  while (i<l) {
      v = v+4;
      v = v-v;
      i = i+1;
  }

  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

  while (v>0) {
      l = l+v;
      l = l+2;
      v = v-1;
  }

}
