int main1(){
  int lpl, io, hy, dw6, e, h, l0r, i7, glx;
  lpl=1;
  io=3;
  hy=60;
  dw6=0;
  e=lpl;
  h=lpl;
  l0r=lpl;
  i7=0;
  glx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dw6 >= 0;
  loop invariant e >= lpl;
  loop invariant i7 <= e + h + l0r;
  loop invariant io >= 3;
  loop invariant glx == 0;
  loop invariant h == 1;
  loop invariant l0r == 1;
  loop invariant lpl == 1;
  loop invariant hy + dw6 == 60;
  loop invariant 0 <= i7;
  loop invariant 0 <= hy <= 60;
  loop assigns dw6, e, hy, io, i7;
*/
while (io<lpl) {
      if (!(!(io%2==0))) {
          if (hy>0) {
              hy--;
              dw6 = dw6 + 1;
          }
      }
      else {
          if (dw6>0) {
              dw6--;
              hy = hy + 1;
          }
      }
      io = io + 1;
      i7++;
      e = e + dw6;
      i7 = e+h+l0r;
      e += 1;
      if (io+1<=glx+lpl) {
          e += 1;
      }
  }
}