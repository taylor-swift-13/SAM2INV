int main1(int o,int q){
  int m05x, rxb, zx;
  m05x=195;
  rxb=m05x;
  zx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m05x == 195;
  loop invariant o == \at(o,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant rxb >= 0;
  loop invariant rxb <= 195;
  loop invariant zx >= 3*(195 - rxb);
  loop invariant zx % 3 == 0;
  loop assigns zx, rxb;
*/
while (rxb>=1) {
      zx = zx*3+3;
      rxb = rxb - 1;
  }
}