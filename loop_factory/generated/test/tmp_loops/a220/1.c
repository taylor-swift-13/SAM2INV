int main1(int k,int m){
  int l, i, v;

  l=13;
  i=0;
  v=m;

  while (i<l) {
      v = v+i;
      v = v+v;
      i = i+1;
  }

  while (v>0) {
      v = v-1;
  }

}
