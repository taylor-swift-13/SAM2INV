int main1(int f){
  int nu, nx;
  nu=f;
  nx=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nu == \at(f, Pre);
  loop invariant nx == 0 || nx == 1;
  loop invariant f == \at(f, Pre) + nu * (1 - nx);
  loop assigns f, nx;
*/
while (nx!=nx) {
      if (nx>nx) {
          nx -= nx;
          nx -= nx;
          nx -= nx;
      }
      else {
          nx -= nx;
          nx -= nx;
          nx -= nx;
      }
      f = f + nu;
  }
}