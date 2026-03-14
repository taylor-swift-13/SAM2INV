int main1(int d,int x){
  int g9, v1vb, r0, b;
  g9=x;
  v1vb=0;
  r0=5;
  b=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v1vb % 6 == 0;
  loop invariant 0 <= v1vb;
  loop invariant g9 == x;
  loop assigns v1vb;
*/
for (; v1vb<=g9-6; v1vb += 6) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v1vb;
  loop invariant (v1vb == 0) ==> (b == \at(d, Pre));
  loop invariant b >= d;
  loop assigns v1vb, b, x;
*/
while (1) {
      if (!(b<r0)) {
          break;
      }
      v1vb = r0-b;
      b += 1;
      x += b;
  }
}