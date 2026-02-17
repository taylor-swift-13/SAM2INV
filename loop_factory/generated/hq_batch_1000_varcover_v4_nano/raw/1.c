int main1(int a,int k,int m){
  int l, i, v;

  l=(k%12)+12;
  i=0;
  v=m;

  while (i<l) {
      v = v-v;
      if (v+6<l) {
          v = v+i;
      }
      i = i+5;
  }

}
