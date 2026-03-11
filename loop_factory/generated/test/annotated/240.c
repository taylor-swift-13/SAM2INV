int main1(int l){
  int m, e, dx, b5, bv;
  m=l;
  e=0;
  dx=0;
  b5=0;
  bv=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dx == b5*l - m*(b5*(b5+1))/2;
  loop invariant l == \at(l, Pre) + b5 * m;
  loop invariant 0 <= b5;
  loop assigns dx, b5, l;
*/
while (b5<m) {
      dx += l;
      b5++;
      l = l + m;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bv - e == 3;
  loop invariant e >= 0;
  loop assigns bv, dx, e;
*/
while (e!=0) {
      bv--;
      dx = dx + m;
      e = e - 1;
  }
}