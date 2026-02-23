int main1(int a,int n){
  int w, q, v, m;

  w=a+23;
  q=2;
  v=0;
  m=n;

  while (v!=0&&m!=0) {
      if (v>m) {
          v = v-m;
      }
      else {
          m = m-v;
      }
  }

}
