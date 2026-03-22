int main1(){
  int u, xb4, ue;
  u=43;
  xb4=0;
  ue=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xb4;
  loop invariant xb4 <= u;
  loop invariant ue == -5 + xb4 * (xb4 - 1) / 2;
  loop invariant u == 43;
  loop assigns ue, xb4;
*/
for (; xb4<=u-1; xb4 = xb4 + 1) {
      ue += xb4;
  }
}