int main1(int b,int k,int m,int q){
  int l, i, v;

  l=q;
  i=0;
  v=m;

  while (i<l) {
      v = 8;
      if (i<v+4) {
          v = v-v;
      }
      else {
          v = v+i;
      }
      i = i+1;
  }

}
