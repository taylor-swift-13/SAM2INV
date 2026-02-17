int main1(int k,int m,int n){
  int l, i, v;

  l=68;
  i=l;
  v=k;

  while (i>0) {
      if ((i%2)==0) {
          v = v+i;
      }
      v = v-l;
      v = v+1;
      v = v+1;
      i = i-1;
  }

}
