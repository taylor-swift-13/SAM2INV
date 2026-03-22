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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qj8 + n == 28;
  loop invariant a == 0;
  loop invariant n == 12 + 2*y8;
  loop invariant 0 <= y8 <= qo;
  loop assigns qj8, n, a, y8, f, uujo;
*/
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