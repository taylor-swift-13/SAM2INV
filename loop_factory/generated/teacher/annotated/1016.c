int main1(int n,int p){
  int e, k, a;

  e=(p%28)+12;
  k=1;
  a=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (\at(p, Pre) % 28) + 12;
  loop invariant p == \at(p, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant a >= 0;
  loop invariant (a % 4 == 0) || (a % 4 == 1);

  loop invariant e == (\at(p, Pre) % 28) + 12 && p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant a >= 0 && ((a % 4 == 0) || (a % 4 == 1));
  loop invariant a % 4 == 0 || a % 4 == 1;
  loop invariant ((a % 4 == 0) || (a % 4 == 1)) && a >= 0;
  loop invariant ( (\at(p, Pre) % 28) + 12 == e ) && p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant a >= 0 && e == \at(p, Pre) % 28 + 12 && p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant e == \at(p, Pre) % 28 + 12;

  loop invariant a >= 0 && (a % 4 == 0 || a % 4 == 1);
  loop assigns a;
*/
while (1) {
      a = a+4;
      if (a+5<e) {
          a = a-a;
      }
  }

}
