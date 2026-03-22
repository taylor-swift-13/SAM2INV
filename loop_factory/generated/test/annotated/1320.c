int main1(){
  int yf, y, l1p3, tu, hd;
  yf=1+22;
  y=0;
  l1p3=1;
  tu=1;
  hd=yf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l1p3 == (y + 1) * (y + 1);
  loop invariant tu == 2 * y + 1;
  loop invariant hd == yf * (y + 1);
  loop invariant 0 <= y <= yf;
  loop assigns y, tu, l1p3, hd;
*/
while (l1p3<=yf) {
      y++;
      tu += 2;
      l1p3 = l1p3 + tu;
      hd = hd + yf;
  }
}