int main1(int b,int m){
  int c, i, v, n;

  c=(b%6)+9;
  i=0;
  v=-8;
  n=b;

  while (v!=0&&n!=0) {
      if (v>n) {
          v = v-n;
      }
      else {
          n = n-v;
      }
  }

}
