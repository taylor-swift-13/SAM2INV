int main1(){
  int js, zykb, y7x, o1, z5j, n37;
  js=1+9;
  zykb=0;
  y7x=1;
  o1=6;
  z5j=zykb;
  n37=zykb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z5j == 2 * n37;
  loop invariant o1 == 6 + n37*(n37 - 1);
  loop invariant 0 <= n37 <= js + 1;
  loop invariant y7x >= 0;
  loop assigns y7x, o1, n37, z5j;
*/
while (1) {
      if (n37>js) {
          break;
      }
      y7x += o1;
      o1 = o1 + z5j;
      y7x = y7x*y7x+y7x;
      n37 = (1)+(n37);
      z5j += 2;
  }
}