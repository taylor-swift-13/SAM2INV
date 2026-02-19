int main1(int a,int q){
  int l, i, v;

  l=(a%33)+6;
  i=l;
  v=6;

  while (i>0) {
      v = v-v;
      i = i-1;
  }

  while (i>0) {
      l = v+a;
      l = l-l;
      i = i-1;
  }

}
