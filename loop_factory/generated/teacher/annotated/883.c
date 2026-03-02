int main1(int k,int n){
  int r, c, x, v;

  r=(k%35)+17;
  c=1;
  x=r;
  v=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant r == (\at(k, Pre) % 35) + 17;

  loop invariant c >= 1;
  loop invariant (c == 1) ==> (x == r);
  loop invariant (c >= 2) ==> (0 <= x && x <= 2);
  loop invariant r == (k % 35) + 17;


  loop invariant k == \at(k,Pre);
  loop invariant n == \at(n,Pre);

  loop invariant r == ((\at(k, Pre) % 35) + 17);
  loop invariant r == \at(k, Pre) % 35 + 17;
  loop invariant c == 1 || (0 <= x && x <= 2);
  loop invariant r == (\at(k,Pre) % 35) + 17;
  loop invariant 1 <= c;
  loop invariant x <= r;

  loop assigns x, c;
*/
while (c+1<=r) {
      x = x*x+x;
      x = x%3;
      c = c+1;
  }

}
