int main1(int n,int y){
  int dn, kb, ux8;
  dn=(n%7)+11;
  kb=0;
  ux8=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ux8 == 1 || ux8 == 2;
  loop invariant n - y == \at(n, Pre) - \at(y, Pre);
  loop invariant dn == (\at(n, Pre) % 7) + 11;
  loop invariant kb == 0;
  loop assigns ux8, n, y;
*/
while (kb+1<=dn) {
      if (ux8==1) {
          ux8 = 2;
      }
      else {
          if (ux8==2) {
              ux8 = 1;
          }
      }
      n = n + ux8;
      y = y + ux8;
  }
}