int main1(int b,int m,int n){
  int l, i, v;

  l=m;
  i=0;
  v=b;

  while (i<l) {
      v = v-v;
      v = v+2;
      if (i+2<=v+l) {
          v = v+v;
      }
      i = i+1;
  }

}
