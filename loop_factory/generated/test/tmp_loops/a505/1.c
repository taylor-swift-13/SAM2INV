int main1(int b,int k){
  int l, i, v;

  l=k-1;
  i=l;
  v=i;

  while (i>0) {
      v = v+v;
      v = v-v;
      i = i-1;
  }

  while (i<l) {
      i = i+1;
  }

}
