int main1(int e){
  int v, omo4, xb, q, y;
  v=e;
  omo4=0;
  xb=0;
  q=0;
  y=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == y * xb;
  loop invariant omo4 == 7 * xb;
  loop invariant y == \at(e, Pre);
  loop assigns e, xb, q, omo4;
*/
while (omo4+7<=v) {
      e = xb+q+y;
      xb += 1;
      q = q + y;
      omo4 = omo4 + 7;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= \at(e, Pre);
  loop assigns y;
*/
while (1) {
      y++;
      if (y>=omo4) {
          break;
      }
  }
}