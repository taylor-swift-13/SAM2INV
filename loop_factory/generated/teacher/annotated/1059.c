int main1(int b,int p){
  int f, q, r;

  f=b;
  q=3;
  r=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == 3;
  loop invariant r == -4;
  loop invariant r % 4 == 0;
  loop invariant b == \at(b, Pre);
  loop invariant f == b;
  loop invariant (q % 4 != 0) ==> r == -4;
  loop invariant (q % 4 == 0) ==> r % 8 == 0;
  loop invariant f == \at(b, Pre) && b == \at(b, Pre) && p == \at(p, Pre) && q == 3;
  loop invariant r % 2 == 0 && r >= -4;
  loop assigns r;
*/
while (1) {
      r = r+2;
      if ((q%4)==0) {
          r = r+r;
      }
      r = r+r;
  }

}
