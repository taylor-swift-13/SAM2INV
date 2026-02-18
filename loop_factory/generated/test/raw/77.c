int main1(int b,int m,int n,int p){
  int l, i, v;

  l=18;
  i=0;
  v=p;

  while (i<l) {
      if (l<b+2) {
          v = v+4;
      }
      v = v-v;
      if ((i%9)==0) {
          v = v-v;
      }
      i = i+1;
  }

}
