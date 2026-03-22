int main1(int e){
  int c, cs9d, a5s, pn, sz, x7l;
  c=e+7;
  cs9d=0;
  a5s=1;
  pn=2;
  sz=0;
  x7l=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(e,Pre) + 7;
  loop invariant a5s == cs9d + 1;
  loop invariant pn == cs9d + 2;
  loop invariant x7l == \at(e,Pre) + 2*(cs9d/5);
  loop invariant c == e + 7;
  loop invariant 5*(x7l - e) == 2*cs9d;
  loop invariant cs9d % 5 == 0;
  loop invariant cs9d >= 0;
  loop invariant x7l == e + 2*(cs9d/5);
  loop assigns a5s, pn, cs9d, x7l, sz;
*/
while (cs9d<c) {
      a5s = a5s + 5;
      pn = pn + 5;
      cs9d = cs9d + 5;
      x7l += 2;
      sz = sz + cs9d;
      sz = sz+x7l+e;
  }
}