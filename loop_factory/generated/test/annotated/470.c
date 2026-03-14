int main1(){
  int a9, z, d, abd, ld;
  a9=1+8;
  z=0;
  d=0;
  abd=a9;
  ld=a9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (d > 0) ==> (abd == d - 1);
  loop invariant d % 2 == 0;
  loop invariant ld == a9 * (d/2 + 1);
  loop assigns abd, d, ld;
*/
while (d<a9) {
      abd = d+1;
      ld += a9;
      d += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ld >= 0);
  loop invariant ld >= a9;
  loop invariant d >= z;
  loop invariant z == 0;
  loop invariant (ld % a9) == 0;
  loop assigns ld, d;
*/
while (z+8<=d) {
      if (z%2==0) {
          ld += a9;
      }
      else {
          ld = ld+a9+1;
      }
      d = ((z+8))+(-(1));
  }
}