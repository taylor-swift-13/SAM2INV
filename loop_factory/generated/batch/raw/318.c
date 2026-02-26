int main1(int b,int k){
  int t, j, s;

  t=80;
  j=0;
  s=-4;

  while (j<=t-1) {
      s = s+2;
      if (j+3<=s+t) {
          s = s-s;
      }
      s = s+j;
  }

}
