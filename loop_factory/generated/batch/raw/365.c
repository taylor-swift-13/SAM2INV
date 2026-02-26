int main1(int b,int n){
  int m, s, k, v;

  m=(b%7)+6;
  s=0;
  k=n;
  v=-4;

  while (s<=m-1) {
      k = k*2;
      v = v/2;
      s = s+1;
  }

}
