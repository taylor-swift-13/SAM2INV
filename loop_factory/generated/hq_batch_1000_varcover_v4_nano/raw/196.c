int main1(int b,int n,int p){
  int l, i, v;

  l=38;
  i=0;
  v=-4;

  while (i<l) {
      if ((i%2)==0) {
          v = v-v;
      }
      else {
          v = v+4;
      }
      i = i+1;
  }

}
