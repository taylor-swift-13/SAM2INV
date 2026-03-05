int main1(int s){
  int ib1, xk2z, ke;
  ib1=s;
  xk2z=ib1;
  ke=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xk2z == \at(s, Pre);
  loop invariant ib1 == \at(s, Pre);
  loop invariant ke % 2 == 0;
  loop invariant s == \at(s,Pre) + (ke/2) * xk2z;
  loop invariant s == ib1 * (1 + ke/2);
  loop invariant ke >= 0;
  loop assigns ke, s;
*/
while (ke<ib1) {
      ke += 2;
      if (ke<=ke) {
          ke = ke;
      }
      s = s + xk2z;
  }
}