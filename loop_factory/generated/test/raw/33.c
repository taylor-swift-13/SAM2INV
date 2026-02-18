int main1(int a,int b,int k,int q){
  int l, i, v;

  l=65;
  i=0;
  v=q;

  while (i<l) {
      v = v+1;
      if (v+3<l) {
          v = v-v;
      }
      i = i+1;
  }

}
