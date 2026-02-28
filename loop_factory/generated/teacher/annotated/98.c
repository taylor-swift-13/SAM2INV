int main1(int n){
  int r, c, y;

  r=50;
  c=r;
  y=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c;
  loop invariant c <= 50;
  loop invariant c % 2 == 0;
  loop invariant r == 50;
  loop invariant n == \at(n, Pre);
  loop invariant c >= 0;
  loop invariant c <= r;
  loop invariant (r - c) % 2 == 0;
  loop invariant c % 2 == r % 2;
  loop assigns c;
*/
while (c-2>=0) {
      c = c-2;
  }

}
