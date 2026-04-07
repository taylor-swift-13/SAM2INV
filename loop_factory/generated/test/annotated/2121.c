int main1(){
  int h, e34, y1rg, ovw;
  h=(1%18)+5;
  e34=0;
  y1rg=0;
  ovw=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ovw == 1;
  loop invariant h == (1 % 18) + 5;
  loop invariant (0 <= e34 && e34 <= h);
  loop invariant (0 <= y1rg && y1rg <= h);
  loop invariant y1rg <= (e34 * ovw);
  loop assigns e34, ovw, y1rg;
*/
while (e34 < h) {
      if (!(!(y1rg + ovw <= h))) {
          y1rg += ovw;
      }
      e34 = e34 + 1;
      ovw = ovw+y1rg-y1rg;
  }
}