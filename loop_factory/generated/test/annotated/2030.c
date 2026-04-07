int main1(){
  int hor, r08, ub, xz, e1z, v1v;
  hor=63;
  r08=hor;
  ub=0;
  xz=0;
  e1z=4;
  v1v=r08;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ub;
  loop invariant ub <= hor;
  loop invariant 0 <= e1z;
  loop invariant (6 * (v1v - 63)) == (ub * (ub + 1) * (13 - ub));
  loop invariant 2*xz == ub*(9 - ub);
  loop invariant e1z + ub == 4;
  loop invariant xz == (ub*(9 - ub))/2;
  loop invariant v1v == 63 + (ub*(ub + 1)*(13 - ub))/6;
  loop invariant 0 <= xz;
  loop assigns ub, xz, e1z, v1v;
*/
while (1) {
      if (!(ub<hor&&e1z>0)) {
          break;
      }
      ub += 1;
      xz += e1z;
      e1z = e1z - 1;
      v1v += xz;
  }
}