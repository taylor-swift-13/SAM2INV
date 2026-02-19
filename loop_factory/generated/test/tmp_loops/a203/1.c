int main1(int b,int k){
  int l, i, v, h;

  l=64;
  i=0;
  v=8;
  h=l;

  while (i<l) {
      v = v+h+h;
      i = i+5;
  }

  while (v>0) {
      i = i+1;
      v = v-1;
  }

}
