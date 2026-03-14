int main1(int u){
  int b, rke, xjn, ra, z, n4;
  b=u;
  rke=3;
  xjn=0;
  ra=(u%28)+10;
  z=rke;
  n4=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n4 - 3*xjn == -6;
  loop invariant xjn >= 0;
  loop invariant z >= 3;
  loop invariant u - xjn == \at(u, Pre);
  loop invariant b == \at(u, Pre);
  loop assigns ra, u, z, xjn, n4;
*/
while (ra>xjn) {
      ra -= xjn;
      u = u + 1;
      z = z + ra;
      xjn = (1)+(xjn);
      n4 = n4 + 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(u, Pre);
  loop assigns xjn;
*/
for (; xjn<=b-2; xjn += 2) {
  }
}