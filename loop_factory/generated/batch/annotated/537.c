int main1(int n,int p){
  int k, f, h, o;

  k=27;
  f=k;
  h=k;
  o=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 27;
  loop invariant (h == k) || (h == 0);
  loop invariant 0 <= f <= k;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant f >= 0;
  loop invariant f <= k;
  loop invariant f <= 27;
  loop invariant h == 0 || h == 27;
  loop invariant 0 <= h <= 27;
  loop invariant 0 <= f <= 27;
  loop assigns f, h;
*/
while (f>=1) {
      h = h*h+h;
      h = h%2;
      f = f-1;
  }

}
