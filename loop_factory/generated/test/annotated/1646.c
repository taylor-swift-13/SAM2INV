int main1(){
  int pl, xv, ox, b;
  pl=1;
  xv=0;
  ox=0;
  b=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b + xv == 3;
  loop invariant ox == 3*xv - xv*(xv - 1)/2;
  loop invariant 0 <= xv;
  loop invariant xv <= pl;
  loop invariant 0 <= ox;
  loop invariant 0 <= b;
  loop assigns ox, xv, b;
*/
while (1) {
      if (!(xv<pl&&b>0)) {
          break;
      }
      ox += b;
      xv++;
      b = b - 1;
  }
}