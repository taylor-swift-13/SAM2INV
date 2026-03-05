int main1(){
  int m, k6pp, w, k7h;
  m=80;
  k6pp=0;
  w=0;
  k7h=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 5 * k6pp;
  loop invariant k6pp <= m;
  loop invariant k7h == 5 * k6pp + 5;
  loop invariant m == 80;
  loop invariant 0 <= k6pp;
  loop assigns w, k7h, k6pp;
*/
while (k6pp<m) {
      w = w + 5;
      k7h = k7h + 5;
      k6pp++;
  }
}