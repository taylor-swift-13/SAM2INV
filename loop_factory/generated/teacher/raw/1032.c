int main1(int k,int m){
  int j, d, r;

  j=15;
  d=0;
  r=j;

  while (1) {
      r = r-r;
      if (r+4<j) {
          r = r+d;
      }
      d = d+1;
  }

}
