int main1(int m,int n){
  int l, i, r;

  l=47;
  i=0;
  r=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant i == 0;
  loop invariant l == 47;
  loop invariant i <= l;

  loop invariant r >= -6;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant r == -6 || r >= 2;
  loop invariant l == 47 && i <= l && r >= -6;
  loop invariant i == 0 && l == 47 && 0 <= i && i <= l;

  loop invariant i == 0 && l == 47 && i <= l;
  loop invariant r >= -6 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant i == 0 && i <= l;
  loop assigns r;
*/
while (i<l) {
      r = r+4;
      r = r*r+r;
  }

}
