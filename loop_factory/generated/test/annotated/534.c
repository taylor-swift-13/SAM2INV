int main1(int a){
  int f, yjq, vc9;
  f=a+24;
  yjq=0;
  vc9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) + yjq * (yjq + 1);
  loop invariant vc9 == 2 * yjq;
  loop invariant f == \at(a, Pre) + 24;
  loop invariant 0 <= yjq;
  loop assigns a, vc9, yjq;
*/
while (yjq<f) {
      vc9 += 2;
      yjq++;
      a += vc9;
  }
}