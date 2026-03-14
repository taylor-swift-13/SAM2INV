int main1(int v){
  int yz, b;
  yz=v+12;
  b=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (yz > 0) ==> (b <= yz);
  loop invariant yz == \at(v, Pre) + 12;
  loop invariant b >= 0;
  loop assigns b;
*/
while (1) {
      b += 1;
      if (b>=yz) {
          break;
      }
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b;
  loop invariant yz == \at(v, Pre) + 12;
  loop assigns b;
*/
while (1) {
      if (!(b<=yz-8)) {
          break;
      }
      b += 8;
  }
}