int main1(int m,int q){
  int l, i, v;

  l=49;
  i=l;
  v=i;

  while (i>0) {
      v = v-v;
      v = v+1;
      i = i-1;
  }

  while (v<l) {
      i = i+v;
      i = i+1;
      v = v+1;
  }

}
