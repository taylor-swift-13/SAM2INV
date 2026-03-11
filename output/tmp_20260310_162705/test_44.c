int main1(int e){
  int n6e, gc, j2, ami, xl;
  n6e=e;
  gc=-4;
  j2=0;
  ami=gc;
  xl=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j2 >= 0;
  loop invariant j2 == 8 * (xl - \at(e, Pre));
  loop invariant (n6e >= 0) ==> j2 <= n6e + 7;
  loop invariant n6e == \at(e, Pre);
  loop invariant ami == (j2*j2)/16 + j2/2 - 4;
  loop invariant e == \at(e, Pre) + (j2*j2)/16 + j2/2;
  loop assigns ami, e, j2, xl;
*/
while (j2<n6e) {
      j2 += 8;
      ami += j2;
      e += j2;
      xl = xl + 1;
  }
/*@
  assert !(j2<n6e) &&
         (j2 >= 0);
*/

}