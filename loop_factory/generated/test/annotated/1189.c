int main1(){
  int wl, x0h, ve, farv, y;
  wl=1;
  x0h=(1%28)+8;
  ve=(1%22)+5;
  farv=0;
  y=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wl == 1;
  loop invariant (x0h % 9) == 0;
  loop invariant 0 <= ve;
  loop invariant 0 <= y;
  loop invariant x0h > 0;
  loop invariant farv + x0h * ve == 54;
  loop assigns farv, ve, x0h, y;
*/
while (ve!=0) {
      if (ve%2==1) {
          farv += x0h;
          ve--;
      }
      x0h = 2*x0h;
      ve = ve/2;
      y = y + wl;
  }
}