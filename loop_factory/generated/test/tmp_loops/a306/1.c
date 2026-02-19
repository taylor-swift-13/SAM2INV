int main1(int p,int q){
  int l, i, v;

  l=p-2;
  i=l;
  v=q;

  while (i>0) {
      v = v+1;
      v = v-v;
      i = i-1;
  }

  while (i<l) {
      i = i+2;
  }

}
