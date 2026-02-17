int main1(int a,int b,int n,int q){
  int l, i, v;

  l=b;
  i=0;
  v=-8;

  while (i<l) {
      if (i<b+3) {
          v = v+1;
      }
      else {
          v = v+v;
      }
      v = v+i;
      if ((i%2)==0) {
          v = v-v;
      }
      i = i+4;
  }

}
