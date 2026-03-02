int main1(int k,int m){
  int y, p, n, c;

  y=(m%21)+12;
  p=y;
  n=0;
  c=8;

  while (p-1>=0) {
      c = y-n;
      n = n+1;
      n = n+4;
      c = c+n;
  }

}
