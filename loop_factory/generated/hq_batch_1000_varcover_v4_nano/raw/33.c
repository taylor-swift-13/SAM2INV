int main1(int k,int m,int n){
  int l, i, v;

  l=76;
  i=0;
  v=n;

  while (i<l) {
      v = v+4;
      if (v+5<l) {
          v = v-v;
      }
      else {
          v = v+v;
      }
      v = v+i;
      i = i+1;
  }

}
