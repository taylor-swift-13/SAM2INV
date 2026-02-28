int main1(int m){
  int n, q, v;

  n=(m%14)+9;
  q=0;
  v=6;

  while (q<=n-3) {
      v = v-v;
      v = v+q;
      q = q+3;
  }

}
