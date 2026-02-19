int main1(int a,int m){
  int l, i, v;

  l=a;
  i=l;
  v=-5;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (l<i) {
      v = v+v;
      v = v-v;
      l = l+1;
  }

}
