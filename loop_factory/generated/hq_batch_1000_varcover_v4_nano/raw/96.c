int main1(int a,int b,int m){
  int l, i, v;

  l=(m%9)+13;
  i=0;
  v=-1;

  while (i<l) {
      v = v-v;
      if (v+2<l) {
          v = a-m;
      }
      v = v+i;
      v = v+1;
      v = v-v;
      i = i+1;
  }

}
