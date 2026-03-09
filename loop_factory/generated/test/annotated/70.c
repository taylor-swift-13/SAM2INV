int main1(int r,int a){
  int nr, dfr, e1yb, fp;
  nr=55;
  dfr=1;
  e1yb=0;
  fp=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dfr >= 1;
  loop invariant e1yb >= 0;
  loop invariant r == \at(r, Pre) + 2*dfr - 2;
  loop invariant dfr <= 2*nr;
  loop invariant fp >= 3;
  loop assigns dfr, e1yb, r, fp;
*/
while (1) {
      if (!(dfr<nr)) {
          break;
      }
      dfr = 2*dfr;
      e1yb = e1yb + 1;
      r += dfr;
      fp = fp*3+(dfr%6)+1;
  }
}