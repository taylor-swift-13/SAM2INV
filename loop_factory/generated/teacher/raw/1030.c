int main1(int b,int m){
  int n, d, j;

  n=(b%37)+5;
  d=0;
  j=m;

  while (1) {
      j = j+4;
      if (j+1<n) {
          j = j%6;
      }
  }

}
