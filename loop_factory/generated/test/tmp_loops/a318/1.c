int main1(int b,int p){
  int l, i, v;

  l=79;
  i=l;
  v=-2;

  while (i>0) {
      v = v-v;
      i = i-1;
  }

  while (v>0) {
      l = l+v;
      v = v-1;
  }

}
