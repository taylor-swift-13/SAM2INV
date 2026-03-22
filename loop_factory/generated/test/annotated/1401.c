int main1(){
  int r, f, b5, y8y3, tjd, d0;
  r=123;
  f=0;
  b5=f;
  y8y3=-6;
  tjd=f;
  d0=f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tjd == 4*d0;
  loop invariant (b5 % 2) == 0;
  loop invariant y8y3 == -6 + 2*d0*(d0 - 1);
  loop invariant 0 <= d0;
  loop invariant d0 <= r + 1;
  loop assigns b5, y8y3, tjd, d0;
*/
while (1) {
      if (d0>r) {
          break;
      }
      b5 = b5 + y8y3;
      y8y3 = (tjd)+(y8y3);
      tjd += 4;
      b5 = b5*2;
      d0++;
  }
}