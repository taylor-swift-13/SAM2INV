int main1(int a,int p){
  int l, i, v;

  l=p+15;
  i=0;
  v=a;

  while (i<l) {
      v = v-p;
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      v = v+3;
      l = l+1;
  }

}
