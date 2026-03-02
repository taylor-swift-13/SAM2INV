int main1(int a,int k){
  int r, u, v, y;

  r=44;
  u=r;
  v=k;
  y=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(k, Pre) + (u - 44);
  loop invariant u == 44 && v == \at(k, Pre) && y == 44;
  loop invariant u - r <= \at(k, Pre) - \at(k, Pre);
  loop invariant y == 44 + 2*(u - 44) + (v - k);
  loop invariant u == 44 && v == \at(k, Pre) && y == 44 && r == 44;

  loop invariant y == 44 + (u - 44) * (u - 44) + (u - 44) * (v - k);
  loop invariant u - r == 44 - 44;
  loop invariant y == 44 + 44 * (u - 44);

  loop invariant u <= r;
  loop invariant v >= k;
  loop invariant u <= r + 1 && v <= \at(k, Pre) + 1;

  loop invariant u - r <= \at(k, Pre) - k + 1;
  loop assigns v, u, y;
*/
while (1) {
      if (u>=r) {
          break;
      }
      v = v+1;
      u = u+1;
      y = y+y;
      y = y+v;
  }

}
