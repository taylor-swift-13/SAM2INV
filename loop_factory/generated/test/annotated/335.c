int main1(){
  int i, qh, x;
  i=10;
  qh=0;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 10 && (0 <= x) && (x <= i) && ((x == 0) || (x == 1));
  loop invariant qh >= 0;
  loop invariant (x == 0) ==> (qh == 0);
  loop invariant (qh == 0) ==> (x == 0);
  loop assigns x, qh;
*/
for (; x>0&&x<=i; qh++) {
      if (x>x) {
          x -= x;
      }
      else {
          x = 0;
      }
      x = x + 1;
  }
}