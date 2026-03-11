int main1(int t,int u){
  int ow, v98, y, d;
  ow=11;
  v98=ow;
  y=1;
  d=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 1 + 6*(v98 - 11);
  loop invariant ow - v98 >= 0;
  loop invariant d - 6*v98 == -59;
  loop assigns d, y, v98;
*/
while (1) {
      if (!(v98<=ow-1)) {
          break;
      }
      d += 6;
      y += 6;
      v98 = v98 + 1;
  }
}