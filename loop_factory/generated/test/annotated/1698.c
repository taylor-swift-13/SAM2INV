int main1(int z){
  int yx, fa, ifq;
  yx=z;
  fa=0;
  ifq=fa;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(z, Pre) + 2*fa;
  loop invariant yx == \at(z, Pre);
  loop invariant ifq == fa * yx + fa * fa + 3 * fa;
  loop invariant 0 <= fa;
  loop assigns fa, z, ifq;
*/
while (fa < yx) {
      ifq += 2;
      z += 2;
      fa++;
      ifq += z;
  }
}