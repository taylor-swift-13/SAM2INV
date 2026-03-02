int main1(int k,int p){
  int l, r, f, s;

  l=k+7;
  r=0;
  f=k;
  s=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre) && p == \at(p, Pre) && l == k + 7;
  loop invariant 2*(s - \at(p, Pre)) == (f - \at(k, Pre))*(f + \at(k, Pre)) && f >= \at(k, Pre);
  loop invariant f*f - \at(k, Pre)*\at(k, Pre) == 2*(s - \at(p, Pre));
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l == \at(k, Pre) + 7;
  loop invariant f >= \at(k, Pre);
  loop invariant 2*(s - \at(p, Pre)) == (f - \at(k, Pre)) * (f + \at(k, Pre));
  loop invariant (f - \at(k, Pre)) % 2 == 0;
  loop invariant 2*(s - p) == (f - k) * (k + f);
  loop invariant f >= k;
  loop invariant (f - k) % 2 == 0;
  loop invariant f * f == k * k + 2 * (s - p);

  loop invariant l == k + 7;
  loop invariant (f - \at(k, Pre)) % 2 == 0 && f >= \at(k, Pre);
  loop invariant 2*(s - \at(p, Pre)) == f*f - \at(k, Pre)*\at(k, Pre);

  loop invariant 2*s - f*f == 2*\at(p, Pre) - \at(k, Pre)*\at(k, Pre);

  loop assigns f, s;
*/
while (1) {
      s = s+f;
      f = f+2;
      s = s+f;
  }

}
