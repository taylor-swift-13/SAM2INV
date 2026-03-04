int main1(){
  int r, d, x21;
  r=1;
  d=0;
  x21=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x21;
  loop invariant x21 <= 6;
  loop invariant d == 0;
  loop invariant r == 1;
  loop invariant x21 >= 0;
  loop invariant 0 <= x21 <= 6;
  loop assigns x21;
*/
while (x21>0) {
      x21--;
      if ((d%9)==0) {
          x21 = r-r;
      }
  }
}