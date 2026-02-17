int main1(int a,int k,int n){
  int l, i, v;

  l=60;
  i=0;
  v=6;

  while (i<l) {
      v = v+v;
      v = v+1;
      if (i+1<=v+l) {
          v = v+1;
      }
      v = v-v;
      i = i+1;
  }

}
