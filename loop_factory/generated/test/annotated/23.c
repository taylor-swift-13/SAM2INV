int main1(){
  int vx;
  vx=-9904;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vx % 2 == 0;
  loop invariant vx + 3 <= 0;
  loop assigns vx;
*/
while (vx+3<0) {
      vx = vx+vx-1;
      vx = vx + 3;
  }
}