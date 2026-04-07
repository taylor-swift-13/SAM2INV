int main1(){
  int aeq, uq, m, z, q4;
  aeq=67;
  uq=0;
  m=aeq;
  z=uq;
  q4=1*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 67 + (uq*(uq+1))/2 + uq*(z+q4);
  loop invariant m == 67 + (uq*(uq+1))/2 + z*uq + q4*uq;
  loop invariant 0 <= uq <= aeq;
  loop invariant aeq == 67;
  loop invariant z == 0;
  loop invariant q4 == 4;
  loop assigns uq, m;
*/
while (uq < aeq) {
      uq += 1;
      if (uq < aeq - 1) {
      }
      if (!(!(uq >= aeq - 1))) {
      }
      else {
      }
      m += uq;
      m = m+z+q4;
  }
}