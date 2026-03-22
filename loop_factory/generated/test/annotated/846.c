int main1(int a,int t){
  int bx, ui, xv, u1f, ii;
  bx=a+17;
  ui=1;
  xv=5;
  u1f=bx;
  ii=ui;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bx == a + 17;
  loop invariant u1f <= bx;
  loop invariant xv >= 5;
  loop invariant (ii == 1) || (ii == 4);
  loop invariant (ui == 1) || (ui == bx);
  loop invariant (ui >= 1);
  loop invariant bx == \at(a,Pre) + 17;
  loop invariant (ui == 1) ==> (u1f == bx);
  loop invariant ((ii == 1 && ui == 1 && u1f == bx && xv == 5 && bx == a + 17) ||
                    (ii == 4 && ui == bx && u1f == bx / 2 && xv == 10 && bx == a + 17));
  loop assigns u1f, xv, ii, ui;
*/
while (1) {
      if (!(ui<bx)) {
          break;
      }
      u1f = u1f/2;
      xv = xv*2;
      ii = ii + 3;
      ui = bx;
  }
}