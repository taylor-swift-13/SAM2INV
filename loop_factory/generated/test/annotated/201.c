int main1(int e){
  int y;
  y=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 0 || y == \at(e, Pre);
  loop invariant (y != 0) ==> (e == \at(e, Pre));
  loop assigns e, y;
*/
while (y!=0&&y!=0) {
      if (y>y) {
          y = y - y;
      }
      else {
          y = y - y;
      }
      e = e + y;
      e = e + e;
  }
}