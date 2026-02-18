int main1(int a,int m,int p,int q){
  int l, i, v;

  l=11;
  i=l;
  v=2;

  while (i>0) {
      v = v-v;
      if ((i%3)==0) {
          v = v-i;
      }
      v = v%3;
      i = i-1;
  }

}
