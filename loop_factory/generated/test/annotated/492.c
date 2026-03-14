int main1(){
  int k6cx, bx, op, an, vwe, yb;
  k6cx=1;
  bx=0;
  op=(1%28)+10;
  an=-3;
  vwe=0;
  yb=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant an <= -3;
  loop invariant bx >= 0;
  loop invariant vwe == 0;
  loop invariant yb == bx - 2;
  loop invariant op == 11 - ((bx*(bx-1))/2);
  loop invariant k6cx == 1;
  loop invariant op >= 1;
  loop assigns op, vwe, bx, an, yb;
*/
while (op>bx) {
      op -= bx;
      vwe = vwe/2;
      bx = (1)+(bx);
      an = an*2;
      yb += k6cx;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yb >= -1;
  loop invariant vwe >= 0;
  loop invariant k6cx == 1;
  loop assigns op, yb, vwe;
*/
while (op>yb) {
      op = op - yb;
      yb = (1)+(yb);
      vwe = vwe + op;
      if ((k6cx%5)==0) {
          vwe = vwe*vwe;
      }
  }
}