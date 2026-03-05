int main1(int b){
  int apz, ap;
  apz=b+20;
  ap=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant apz == \at(b, Pre) + 20;
  loop invariant b == \at(b, Pre) + apz * ap;
  loop invariant ap >= 0;
  loop invariant apz >= 0 ==> (0 <= ap && ap <= apz);
  loop assigns ap, b;
*/
while (ap<apz) {
      ap += 1;
      if (ap<=ap) {
          ap = ap;
      }
      b = b + apz;
  }
}