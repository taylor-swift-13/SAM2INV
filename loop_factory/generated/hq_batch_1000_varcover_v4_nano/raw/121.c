int main1(int a,int p,int q){
  int l, i, v;

  l=34;
  i=0;
  v=l;

  while (i<l) {
      v = v+v;
      if (v+2<l) {
          v = v+1;
      }
      v = v+i;
      v = v-v;
      i = i+1;
  }

}
