int main1(){
  int qo, y8, qj8, n, a, uujo, f, ek1;

  qo=1-1;
  y8=qo;
  qj8=16;
  n=12;
  a=0;
  uujo=qo;
  f=qo;
  ek1=y8;

  while (y8<qo) {
      if (!(a!=0)) {
          qj8 -= 2;
          n += 2;
          a = 0;
      }
      else {
          qj8 += 2;
          n -= 2;
          a = 1;
      }
      y8 = y8 + 1;
      if (qo<n+3) {
          f = uujo-f;
      }
      uujo += n;
      uujo = uujo+f+ek1;
  }

}
