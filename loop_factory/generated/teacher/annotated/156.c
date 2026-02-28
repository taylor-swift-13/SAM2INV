int main1(int n){
  int r, o, a;

  r=35;
  o=0;
  a=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o % 4 == 0;

  loop invariant r == 35;
  loop invariant a >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant a % 5 == 0;
  loop invariant 0 <= o;
  loop invariant o <= r + 3;
  loop invariant 0 <= a;
  loop invariant o >= 0;
  loop invariant a >= (5*o)/4;

  loop assigns a, o;
*/
while (o<r) {
      a = a+a;
      a = a+5;
      o = o+4;
  }

}
