int main1(int m,int p){
  int l, i, v;

  l=m-5;
  i=0;
  v=0;

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+5;
  }

  while (v>0) {
      i = i+6;
      i = i-i;
      v = v-1;
  }

}
