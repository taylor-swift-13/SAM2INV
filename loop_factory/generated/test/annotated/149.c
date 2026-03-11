int main1(int n){
  int om45, vp1a, z3, eyc;
  om45=n-5;
  vp1a=0;
  z3=0;
  eyc=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z3 == 4 * vp1a;
  loop invariant eyc == 4 + 4 * vp1a;
  loop invariant om45 == \at(n, Pre) - 5;
  loop invariant om45 == n - 5;
  loop invariant vp1a >= 0;
  loop invariant (om45 >= 0) ==> (vp1a <= om45);
  loop assigns vp1a, z3, eyc;
*/
while (1) {
      if (!(vp1a<om45)) {
          break;
      }
      vp1a++;
      z3 += 4;
      eyc += 4;
  }
}