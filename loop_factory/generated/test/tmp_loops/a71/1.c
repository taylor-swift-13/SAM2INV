int main1(int n,int p){
  int l, i, v;

  l=p;
  i=l;
  v=-5;

  while (i>0) {
      v = v-v;
      v = v+2;
      i = i-1;
  }

  while (v<i) {
      l = l+1;
      v = v+2;
  }

}
