int main1(int b,int p){
  int y, t, a;

  y=(b%14)+17;
  t=0;
  a=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0 && a >= 0 && y == \at(b, Pre) % 14 + 17;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant (a % 2) == 0;
  loop invariant a >= 0;
  loop invariant t == 0;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant y == (\at(b, Pre) % 14) + 17;
  loop invariant y == \at(b, Pre) % 14 + 17;
  loop invariant a % 2 == 0;
  loop invariant a % 2 == 0 && t == 0 && y == (\at(b, Pre) % 14) + 17;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre) && a >= 0;


  loop assigns a;
*/
while (1) {
      a = a+4;
      a = a+t;
      if (a+4<y) {
          a = a%2;
      }
  }

}
