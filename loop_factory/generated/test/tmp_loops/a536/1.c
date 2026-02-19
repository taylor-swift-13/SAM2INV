int main1(int a,int m){
  int l, i, v;

  l=a;
  i=l;
  v=a;

  while (i>0) {
      v = v+i;
      v = v-v;
      i = i-1;
  }

  while (v<l) {
      i = i-i;
      i = i+i;
      v = v+3;
  }

}
