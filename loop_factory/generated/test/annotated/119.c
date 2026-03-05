int main1(int c,int n){
  int qn0, iq1, v0;
  qn0=(c%37)+12;
  iq1=2;
  v0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 <= iq1;
  loop invariant v0 <= iq1 - 1;
  loop invariant c == \at(c, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant qn0 == (c % 37) + 12;
  loop invariant v0 <= 4;
  loop invariant v0 % 4 == (iq1 - 2) % 4;
  loop invariant v0 >= 0;
  loop invariant (iq1 == 2) ==> (v0 == 0);
  loop assigns v0, iq1;
*/
while (iq1<qn0) {
      v0++;
      if (v0>=5) {
          v0 = v0 - 5;
          v0++;
      }
      iq1 = iq1 + 1;
  }
}