int main1(int x){
  int vsn, ke, xj6, q, k0v;
  vsn=148;
  ke=0;
  xj6=-8;
  q=vsn;
  k0v=vsn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k0v == q;
  loop invariant 0 <= ke;
  loop invariant ke <= vsn;
  loop invariant xj6 + k0v == 140;
  loop invariant xj6 == vsn - q - 8;
  loop assigns x, xj6, q, k0v, ke;
*/
while (1) {
      if (!(ke < vsn)) {
          break;
      }
      x = (xj6 = xj6 - 1, q = q - 1, k0v = k0v - 1, ke = ke + 1);
      xj6 += 2;
      ke = vsn;
  }
}