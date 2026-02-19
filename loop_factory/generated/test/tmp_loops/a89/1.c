int main1(int a,int p){
  int l, i, v;

  l=36;
  i=0;
  v=0;

  while (i<l) {
      v = v-v;
      i = i+1;
  }

  while (v<l) {
      i = i+v;
      v = v+1;
  }

}
