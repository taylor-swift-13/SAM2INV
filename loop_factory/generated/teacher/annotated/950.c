int main1(int a,int b){
  int r, v, q;

  r=a+6;
  v=0;
  q=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (q == a) || (q == -6);
  loop invariant r == a + 6;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == -6 || q == a;
  loop invariant r == \at(a, Pre) + 6;
  loop invariant q == a || q == -6;
  loop invariant q == \at(a, Pre) || q == -6;
  loop invariant a == \at(a,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant r == \at(a,Pre) + 6;
  loop assigns q;
*/
while (1) {
      q = q+2;
      q = a;
  }

}
