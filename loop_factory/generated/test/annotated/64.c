int main1(){
  int s, x26s, mtk, yb, lr;
  s=1;
  x26s=0;
  mtk=x26s;
  yb=x26s;
  lr=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yb == mtk;
  loop invariant s >= x26s;
  loop invariant (s - x26s) <= 1;
  loop invariant lr == 8 + yb*(yb+1)/2;
  loop invariant x26s == 0;
  loop assigns yb, mtk, lr, s;
*/
while (1) {
      if (!(x26s+1<=s)) {
          break;
      }
      yb = yb + 1;
      mtk += 1;
      lr += mtk;
      s = (x26s+1)-1;
  }
}