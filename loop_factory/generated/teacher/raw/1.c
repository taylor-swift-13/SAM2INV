int main1(int a,int n){
  int r, i, v;

  r=63;
  i=0;
  v=0;

  while (i<r) {
      if (v+1<r) {
          v = v-v;
      }
      i = i+1;
  }

}
