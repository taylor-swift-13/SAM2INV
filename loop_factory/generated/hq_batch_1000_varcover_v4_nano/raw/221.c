int main1(int a,int m,int n){
  int l, i, v;

  l=16;
  i=l;
  v=l;

  while (i>0) {
      v = v+v;
      v = v-v;
      v = v-v;
      v = v-v;
      v = v+1;
      i = i-1;
  }

}
