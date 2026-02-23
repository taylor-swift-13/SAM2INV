int main1(int a,int k){
  int n, i, s;

  n=k;
  i=0;
  s=-4;

  while (i<n) {
      if (s+6<n) {
          s = s-s;
      }
      else {
          s = s+i;
      }
      i = i+1;
  }

}
