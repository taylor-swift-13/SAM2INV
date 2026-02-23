int main1(int b,int n){
  int m, t, e, c;

  m=(b%38)+12;
  t=0;
  e=b;
  c=-5;

  while (t<=m-1) {
      e = e*4+2;
      c = c*e+2;
      e = e*3;
  }

}
