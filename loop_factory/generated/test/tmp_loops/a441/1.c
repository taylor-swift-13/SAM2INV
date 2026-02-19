int main1(int n,int p){
  int l, i, v;

  l=p;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (i<l) {
      v = v-v;
      i = i+2;
  }

}
