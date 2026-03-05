int main1(int v,int n){
  int vy, vd, b6, u;
  vy=n;
  vd=0;
  b6=3;
  u=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= vy;
  loop invariant vy == \at(n, Pre);
  loop invariant n >= \at(n,Pre) + vd*3;
  loop invariant n <= \at(n,Pre) + vd*11;
  loop invariant 3 <= b6 && b6 <= 11 && (u == 1 || u == -1) && 0 <= vd && (vy >= 0 ==> vd <= vy);
  loop invariant n >= vy + 3*vd;
  loop invariant n <= vy + 11*vd;
  loop invariant u == 1 || u == -1;
  loop assigns b6, vd, n, u;
*/
while (vd<vy) {
      if (b6>=11) {
          u = -1;
      }
      if (b6<=3) {
          u = 1;
      }
      b6 = b6 + u;
      vd += 1;
      n += b6;
  }
}