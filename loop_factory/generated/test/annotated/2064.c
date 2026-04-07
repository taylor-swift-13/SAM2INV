int main1(){
  int z, p0, azg;
  z=64;
  p0=0;
  azg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant azg == 6 * p0 + (p0 / 2);
  loop invariant 0 <= p0 <= z;
  loop assigns p0, azg;
*/
while (p0 < z) {
      p0++;
      if (p0 % 2 == 0) {
          azg++;
      }
      azg += 6;
  }
}