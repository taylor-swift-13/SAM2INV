int main1(int b,int m){
  int l, q, v, t;

  l=80;
  q=2;
  v=m;
  t=b;

  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
  }

}
