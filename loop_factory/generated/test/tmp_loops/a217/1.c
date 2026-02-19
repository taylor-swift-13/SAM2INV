int main1(int n,int p){
  int l, i, v;

  l=(p%14)+5;
  i=0;
  v=i;

  while (i<l) {
      v = v+1;
      v = v-v;
      i = i+1;
  }

  while (v<i) {
      v = v+1;
  }

}
