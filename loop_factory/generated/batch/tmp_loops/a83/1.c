int main1(int a,int n){
  int h, k, v, i;

  h=56;
  k=1;
  v=k;
  i=a;

  while (v!=0&&i!=0) {
      if (v>i) {
          v = v-i;
      }
      else {
          i = i-v;
      }
      v = v*2;
      i = i/2;
  }

}
