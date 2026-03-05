int main1(int s){
  int qs, a3;
  qs=s+19;
  a3=qs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a3 == qs;
  loop invariant qs == \at(s, Pre) + 19;
  loop invariant (qs != 0) ==> ((s - \at(s, Pre)) % qs == 0);
  loop assigns a3, s;
*/
while (a3<qs&&a3>0) {
      a3++;
      a3 -= 1;
      s += qs;
  }
}