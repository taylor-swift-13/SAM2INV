int main1(int b,int k){
  int m, u, v, a;

  m=(k%34)+12;
  u=m+3;
  v=0;
  a=0;

  while (v<m) {
      if (v<m/2) {
          a = a+2;
      }
      else {
          a = a-2;
      }
      v = v+1;
  }

}
