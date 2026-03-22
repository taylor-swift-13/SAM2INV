int main1(){
  int au, d1y, ur, v;
  au=(1%28)+8;
  d1y=(1%22)+5;
  ur=0;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant ur >= 0;
  loop invariant ur + au * d1y == 54;
  loop invariant au >= 9;
  loop invariant ur <= au;
  loop invariant au % 9 == 0;
  loop assigns au, d1y, ur, v;
*/
while (1) {
      if (!(d1y!=0)) {
          break;
      }
      if (d1y%2==1) {
          ur += au;
          d1y--;
      }
      d1y = d1y/2;
      au = 2*au;
      v += d1y;
  }
}