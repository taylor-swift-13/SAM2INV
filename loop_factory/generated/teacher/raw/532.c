int main1(int b,int n){
  int m, t, e, c;

  m=(b%38)+12;
  t=0;
  e=0;
  c=b;

  while (1) {
      c = m-e;
      e = e+1;
      e = e+c;
      c = c+c;
      c = c+4;
      e = c+t;
  }

}
