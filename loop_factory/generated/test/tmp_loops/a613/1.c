int main1(int a,int m){
  int l, i, v;

  l=(a%28)+4;
  i=l;
  v=l;

  while (i>0) {
      v = v-v;
      i = i-1;
  }

  while (i<v) {
      l = l+1;
      l = l-l;
      i = i+1;
  }

}
