int main1(int b,int m,int p){
  int l, i, v;

  l=(b%6)+15;
  i=0;
  v=m;

  while (i<l) {
      v = v+1;
      v = v-v;
      v = v-v;
      v = v+i;
      v = v+i;
      i = i+1;
  }

}
