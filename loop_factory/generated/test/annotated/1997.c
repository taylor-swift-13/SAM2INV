int main1(int m){
  int b, z9, zm5, ihli, bdj;
  b=m+6;
  z9=0;
  zm5=-m;
  ihli=b;
  bdj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ihli == b + z9;
  loop invariant bdj == (-\at(m, Pre)) * z9 + (z9 * (z9 + 1)) / 2;
  loop invariant z9 >= 0;
  loop invariant ((zm5 - z9) == (-m));
  loop invariant (bdj == (-m * z9 + (z9 * (z9 + 1)) / 2));
  loop invariant zm5 == -\at(m, Pre) + z9;
  loop invariant (b >= 0) ==> (z9 <= b);
  loop assigns ihli, z9, zm5, bdj;
*/
while (z9 < b && zm5 < 0) {
      ihli += 1;
      z9 += 1;
      zm5 += 1;
      bdj += zm5;
  }
}