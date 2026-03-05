int main1(){
  int a, jrh, y1x;
  a=(1%12)+11;
  jrh=0;
  y1x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 12;
  loop invariant 0 <= y1x <= 1;
  loop invariant jrh >= 0;
  loop invariant y1x > 0 ==> y1x == 1 && jrh >= 0;
  loop assigns jrh, y1x;
*/
for (; y1x>0&&y1x<=a; jrh = jrh + 1) {
      if (y1x>y1x) {
          y1x -= y1x;
      }
      else {
          y1x = 0;
      }
      y1x += 1;
  }
}