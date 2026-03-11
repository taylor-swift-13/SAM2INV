int main1(){
  int rh, ly8, ov, z0y;
  rh=64;
  ly8=0;
  ov=rh;
  z0y=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ly8 == 0;
  loop invariant z0y == 13;
  loop invariant rh >= ly8 + 5;
  loop invariant ov >= 64;
  loop invariant ov >= rh;
  loop invariant rh >= 0;
  loop assigns ov, rh;
*/
while (ly8+6<=rh) {
      if (ly8<rh/2) {
          ov = ov + z0y;
      }
      else {
          ov++;
      }
      rh = (ly8+6)-1;
  }
}