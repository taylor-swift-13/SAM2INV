int main1(){
  int gmp, ty;
  gmp=1+22;
  ty=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ty;
  loop invariant ty <= 7;
  loop invariant gmp == 1 + 22;
  loop assigns ty;
*/
while (ty<gmp) {
      ty = (ty+1)%7;
      ty = ty + 1;
  }
}