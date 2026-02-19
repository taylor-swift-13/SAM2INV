int main1(int b,int q){
  int l, i, v;

  l=(q%29)+12;
  i=l;
  v=-8;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (l<i) {
      v = v+1;
      v = v-v;
      l = l+1;
  }

}
