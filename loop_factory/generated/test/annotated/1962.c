int main1(){
  int z, e7, pm, y9ty;
  z=75;
  e7=0;
  pm=0;
  y9ty=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= e7;
  loop invariant e7 <= z;
  loop invariant pm == (e7 % 2);
  loop invariant 2*y9ty == e7 + (e7 % 2);
  loop invariant 0 <= y9ty;
  loop invariant y9ty <= e7;
  loop invariant (pm == 0) || (pm == 1);
  loop invariant y9ty == ((e7 + pm) / 2);
  loop assigns e7, pm, y9ty;
*/
while (e7<z) {
      e7 = e7 + 1;
      pm = 1-pm;
      y9ty = y9ty + pm;
  }
}