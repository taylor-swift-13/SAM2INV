int main1(int h,int f){
  int r, b2, s03, fn;
  r=(f%13)+10;
  b2=1;
  s03=0;
  fn=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (fn - \at(h, Pre) == s03);
  loop invariant fn == h + s03;
  loop invariant r == (f % 13) + 10;
  loop invariant (s03 == 0) ==> (b2 == 1);
  loop invariant (s03 != 0) ==> (b2 == r);
  loop invariant 0 <= s03 <= 1;
  loop assigns b2, s03, fn;
*/
while (b2<r) {
      s03++;
      fn += b2;
      b2 = r;
  }
}