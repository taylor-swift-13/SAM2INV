int main1(int p,int q){
  int h, d, n, c;

  h=48;
  d=h+6;
  n=d;
  c=4;

  while (n!=0&&c!=0) {
      if (n>c) {
          n = n-c;
      }
      else {
          c = c-n;
      }
      n = n*4+1;
  }

}
