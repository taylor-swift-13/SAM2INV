int main1(int a,int n){
  int r, c, v;

  r=44;
  c=r;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 44 - 4*(v - a);
  loop invariant v >= a;
  loop invariant c + 4*v == 44 + 4*a;
  loop invariant v - a <= 11;
  loop invariant 0 <= c;
  loop invariant c <= 44;
  loop invariant c % 4 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant r == 44;
  loop invariant v == a + (44 - c)/4;
  loop invariant c >= 0;
  loop invariant (44 - c) % 4 == 0;
  loop assigns v, c;
*/
while (c>=4) {
      v = v+1;
      c = c-4;
  }

}
