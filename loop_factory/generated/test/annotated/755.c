int main1(){
  int e3, xw, j, x;
  e3=(1%20)+1;
  xw=(1%25)+1;
  j=0;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant j <= e3;
  loop invariant xw >= 0;
  loop invariant e3 % 2 == 0;
  loop invariant x >= 0;
  loop invariant xw <= 2;
  loop invariant 0 <= e3;
  loop assigns e3, xw, j, x;
*/
while (xw!=0) {
      if (xw%2==1) {
          j += e3;
          xw = xw - 1;
      }
      else {
      }
      xw = xw/2;
      e3 = 2*e3;
      x = x*4+(xw%7)+0;
      x = x*x+x;
  }
}