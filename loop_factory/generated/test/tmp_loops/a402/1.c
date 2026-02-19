int main1(int a,int n){
  int l, i, v;

  l=n-2;
  i=0;
  v=a;

  while (i<l) {
      v = v+5;
      v = v+1;
      i = i+1;
  }

  while (v>0) {
      i = i+1;
      i = i+v;
      v = v-1;
  }

}
