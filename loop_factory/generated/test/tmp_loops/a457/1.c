int main1(int b,int q){
  int l, i, v;

  l=47;
  i=l;
  v=-5;

  while (i>0) {
      v = v+2;
      i = i/2;
  }

  while (v>0) {
      l = l+v;
      v = v-1;
  }

}
