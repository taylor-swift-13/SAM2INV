int main1(int a,int m){
  int l, i, v;

  l=a;
  i=0;
  v=m;

  while (i<l) {
      v = v-v;
      v = v+5;
      i = i+4;
  }

  while (v<l) {
      i = i+1;
      i = i+i;
      v = v+1;
  }

}
