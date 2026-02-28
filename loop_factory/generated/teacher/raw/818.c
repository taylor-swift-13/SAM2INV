int main1(int b,int k){
  int n, q, v, u;

  n=(k%11)+20;
  q=3;
  v=0;
  u=0;

  while (v<n) {
      if (v<n/2) {
          u = u+3;
      }
      else {
          u = u-3;
      }
      v = v+1;
  }

}
