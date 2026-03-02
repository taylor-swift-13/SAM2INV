int main1(int a,int k){
  int r, n, f;

  r=42;
  n=1;
  f=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 1;
  loop invariant n <= r;
  loop invariant n == 1 || n % 2 == 0;
  loop invariant r == 42;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n >= 1 && (n == 1 || n % 2 == 0) && n <= r;
  loop invariant r == 42 && a == \at(a, Pre) && k == \at(k, Pre);
  loop invariant r == 42 && n >= 1 && n <= r;

  loop invariant n >= 1 && n <= r && (n == 1 || n % 2 == 0);
  loop invariant n >= 1 && n <= r;
  loop invariant (n == 1) || (n % 2 == 0);
  loop assigns n;
*/
while (n*2<=r) {
      n = n*2;
  }

}
