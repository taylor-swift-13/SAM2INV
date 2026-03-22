int main1(){
  int pr, a99, vukl, kyr, gc73, a;
  pr=1;
  a99=pr;
  vukl=38;
  kyr=0;
  gc73=1;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vukl + kyr == 38;
  loop invariant vukl >= 0;
  loop invariant kyr >= 0;
  loop invariant a99 >= 1;
  loop invariant gc73 == a99;
  loop invariant a99 <= pr;
  loop invariant a >= 0;
  loop invariant pr == 1;
  loop assigns a, kyr, a99, gc73, vukl;
*/
while (1) {
      if (!(vukl>0&&a99<pr)) {
          break;
      }
      if (vukl<=gc73) {
          a = vukl;
      }
      else {
          a = gc73;
      }
      kyr = kyr + a;
      a99++;
      gc73 += 1;
      vukl = vukl - a;
  }
}