int main1(int m,int p){
  int a, r, b, t;

  a=m+9;
  r=a;
  b=r;
  t=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b - t <= 7;
  loop invariant a == m + 9;
  loop invariant r == a;
  loop invariant t <= b;
  loop invariant b >= r;
  loop invariant t >= b - 7;
  loop invariant (b - r) % 7 == 0;
  loop invariant m == \at(m,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant (t == b) || (b == t + 7);
  loop invariant a == \at(m, Pre) + 9;
  loop invariant b >= t;
  loop invariant (b - t == 0) || (b - t == 7) && r >= 3;
  loop assigns b, t;
*/
while (r>3) {
      t = b;
      b = b+2;
      b = b+5;
  }

}
