int main1(int b,int p){
  int y, t, a;

  y=(b%14)+17;
  t=0;
  a=2;

  while (1) {
      a = a+4;
      a = a+t;
      if (a+4<y) {
          a = a%2;
      }
  }

}
