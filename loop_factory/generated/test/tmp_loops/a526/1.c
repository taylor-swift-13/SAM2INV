int main1(int k,int q){
  int l, i, v, o;

  l=(q%26)+12;
  i=0;
  v=1;
  o=i;

  while (i<l) {
      v = v+1;
      o = o-1;
  }

  while (o<l) {
      v = v-v;
      o = o+5;
  }

}
