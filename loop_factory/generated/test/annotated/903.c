int main1(int d){
  int i, ulbq, g, p;
  i=33;
  ulbq=0;
  g=0;
  p=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 33;
  loop invariant 0 <= ulbq;
  loop invariant ulbq <= i;
  loop invariant g == ulbq*(ulbq - 1)/2;
  loop invariant p == 3 + ulbq*(ulbq + 1)/2;
  loop invariant d == \at(d,Pre) + ulbq*(ulbq + 1)/2;
  loop assigns g, ulbq, p, d;
*/
while (1) {
      if (!(ulbq<i)) {
          break;
      }
      g += ulbq;
      ulbq++;
      p += ulbq;
      d += ulbq;
  }
}