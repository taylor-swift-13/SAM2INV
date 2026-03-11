int main1(int c,int v){
  int j, orp, a, lp, xe, k;

  j=57;
  orp=2;
  a=0;
  lp=0;
  xe=0;
  k=4;

  while (orp<j) {
      lp = orp%5;
      if (!(!(orp>=k))) {
          xe = (orp-k)%5;
          a = a+lp-xe;
      }
      else {
          a += lp;
      }
      k = k + xe;
      orp++;
  }

}
