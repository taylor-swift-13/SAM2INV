int main1(int m){
  int ue, u, dv;
  ue=51;
  u=0;
  dv=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dv - 2*u == 2;
  loop invariant m - \at(m, Pre) == u*(u+1)/2;
  loop invariant 0 <= u;
  loop invariant u <= ue;
  loop invariant dv == 2*u + 2;
  loop invariant m == \at(m, Pre) + u*(u+1)/2;
  loop invariant dv == 2 + 2*u;
  loop invariant dv == 2 * (u + 1);
  loop invariant ue == 51;
  loop invariant u >= 0;
  loop assigns dv, u, m;
*/
while (1) {
      if (!(u<ue)) {
          break;
      }
      dv += 2;
      u = u + 1;
      m = m + u;
  }
}