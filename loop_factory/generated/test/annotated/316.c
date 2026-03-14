int main1(int w){
  int jnl, pu6, pq7, w4;
  jnl=61;
  pu6=jnl;
  pq7=-4;
  w4=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w4 == -240 + 4*pu6;
  loop invariant w4 + pq7 * pu6 == -240;
  loop invariant jnl == 61;
  loop invariant 0 <= pu6 <= 61;
  loop assigns w4, pu6;
*/
while (1) {
      if (!(pu6>0)) {
          break;
      }
      w4 = w4+pq7*pu6;
      pu6 = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pu6 - w * jnl == -61 * w;
  loop invariant jnl >= 61;
  loop invariant w4 == -240;
  loop assigns jnl, pu6;
*/
while (1) {
      if (!(jnl<=w4-1)) {
          break;
      }
      jnl = jnl + 1;
      pu6 = pu6 + w;
  }
}