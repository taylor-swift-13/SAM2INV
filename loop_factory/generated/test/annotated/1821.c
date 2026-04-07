int main1(int a){
  int nfj, zy0, w0, kf, d7f8;
  nfj=9;
  zy0=0;
  w0=nfj;
  kf=0;
  d7f8=(a%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w0 == 9 + kf;
  loop invariant zy0 >= 0;
  loop invariant a >= \at(a,Pre);
  loop invariant kf >= 0;
  loop invariant w0 == kf + nfj;
  loop invariant d7f8 <= ((\at(a, Pre) % 35) + 8);
  loop assigns a, d7f8, kf, w0, zy0;
*/
while (1) {
      if (!(d7f8>=1)) {
          break;
      }
      zy0 = zy0+w0*w0;
      kf = kf+d7f8*d7f8;
      w0 = w0+d7f8*d7f8;
      d7f8 -= 1;
      a = a+d7f8+zy0;
  }
}