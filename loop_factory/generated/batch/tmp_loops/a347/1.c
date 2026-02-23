int main1(int a,int n){
  int s, k, v, e;

  s=a-2;
  k=0;
  v=-3;
  e=k;

  while (k<s) {
      if (v+2<=s) {
          v = v+2;
      }
      else {
          v = s;
      }
      v = v*2;
  }

}
