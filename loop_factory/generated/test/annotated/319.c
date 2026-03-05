int main1(int p,int r){
  int i, ikm, xb, u;
  i=32;
  ikm=i;
  xb=0;
  u=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 32;
  loop invariant (ikm - u) == 31;
  loop invariant 0 <= xb <= i;
  loop invariant 1 <= u <= i + 1;
  loop assigns xb, u, ikm;
*/
while (xb>0&&u<=i) {
      if (xb>u) {
          xb = xb - u;
      }
      else {
          xb = 0;
      }
      xb += 1;
      u = u + 1;
      ikm = ikm + 1;
  }
}