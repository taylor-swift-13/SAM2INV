int main1(int p){
  int vld, gj9, l3ci, j15c, jrb;
  vld=p+13;
  gj9=vld;
  l3ci=1;
  j15c=0;
  jrb=p*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j15c == (l3ci - 1) * l3ci * (2 * l3ci - 1) / 6;
  loop invariant p == \at(p, Pre) + (l3ci - 1) * vld;
  loop invariant jrb == 3 * \at(p, Pre) + 3 * (l3ci - 1);
  loop invariant vld == \at(p, Pre) + 13;
  loop invariant gj9 == vld;
  loop assigns j15c, jrb, p, l3ci;
*/
while (l3ci<=vld) {
      j15c = j15c+l3ci*l3ci;
      jrb = jrb + 3;
      p += gj9;
      l3ci = l3ci + 1;
  }
}