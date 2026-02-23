int main1(int m,int p){
  int a, r, b, t;

  a=m+9;
  r=a;
  b=r;
  t=r;

  while (r>3) {
      if (b+3<=a) {
          b = b+3;
      }
      else {
          b = a;
      }
      b = b+5;
  }

}
