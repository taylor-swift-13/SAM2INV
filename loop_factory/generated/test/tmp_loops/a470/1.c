int main1(int a,int q){
  int l, i, v;

  l=a+20;
  i=l;
  v=q;

  while (i>0) {
      v = v+1;
      v = v-v;
      i = i-1;
  }

  while (l<i) {
      l = l+1;
  }

}
