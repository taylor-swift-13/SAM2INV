int main1(int m,int n,int p){
  int l, i, v;

  l=p;
  i=l;
  v=l;

  while (i>0) {
      v = v-v;
      v = v+3;
      if ((i%4)==0) {
          v = v-v;
      }
      v = v-v;
      v = v-v;
      i = i-1;
  }

}
