int main1(){
  int zibi, yg, l2, v, y;
  zibi=1-4;
  yg=0;
  l2=1;
  v=0;
  y=yg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l2 >= 2*v;
  loop invariant l2 >= 1;
  loop invariant v >= 0;
  loop invariant y >= 0;
  loop invariant zibi == -3;
  loop assigns v, l2, y;
*/
while (1) {
      if (!(l2<=zibi-1)) {
          break;
      }
      v = (1)+(v);
      l2 = 2*l2;
      y = y*3+(l2%5)+3;
  }
}