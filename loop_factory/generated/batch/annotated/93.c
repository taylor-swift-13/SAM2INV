int main1(int a,int q){
  int n, h, f;

  n=25;
  h=0;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= 0;

  loop invariant h % 3 == 0;
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant n == 25;
  loop invariant f == 25 || f == (q % 3) + 6;
  loop invariant (h % 3 == 0);

  loop invariant ((h == 0) ==> (f == 25));

  loop invariant (0 <= h);
  loop invariant h <= 27;
  loop invariant 0 <= h;
  loop invariant h <= n + 2;
  loop assigns f, h;
*/
while (h<n) {
      f = q%3;
      f = f+6;
      h = h+3;
  }

}
