int main1(int k,int m){
  int f, x, v, q;

  f=33;
  x=f;
  v=x;
  q=f;

  while (v!=0&&q!=0) {
      if (v>q) {
          v = v-q;
      }
      else {
          q = q-v;
      }
  }

}
