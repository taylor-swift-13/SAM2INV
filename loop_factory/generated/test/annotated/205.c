int main1(int g,int q){
  int zz, x19, ia, u, hk, y;
  zz=107;
  x19=0;
  ia=1;
  u=3;
  hk=0;
  y=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hk == x19 * (ia - 1);
  loop invariant u == 3 + ((ia - 1) * ia * (2 * ia - 1)) / 6;
  loop invariant 1 <= ia <= zz + 1;
  loop invariant hk == 0;
  loop assigns hk, ia, u;
*/
while (ia<=zz) {
      u = u+ia*ia;
      hk += x19;
      ia++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= q;
  loop invariant u - (ia - 108) * zz == 414093;
  loop invariant ia == 108;
  loop invariant x19 == 0;
  loop assigns y, ia, u;
*/
while (1) {
      if (!(ia<=x19)) {
          break;
      }
      y = y+ia*ia;
      u += zz;
      ia++;
  }
}