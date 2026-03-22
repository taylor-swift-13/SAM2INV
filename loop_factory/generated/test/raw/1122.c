int main1(int c,int d){
  int ir, k5hc, a, bs, n3;

  ir=c*4;
  k5hc=0;
  a=0;
  bs=0;
  n3=k5hc;

  while (bs<ir) {
      bs = bs + 1;
      a = a + c;
      c = c+(bs%8);
  }

  while (ir<a) {
      n3 = n3 + c;
      ir = ir + 1;
      c = c + n3;
  }

}
