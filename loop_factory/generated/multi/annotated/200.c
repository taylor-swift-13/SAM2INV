int main1(int b,int m){
  int l, s, k;

  l=35;
  s=0;
  k=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 35;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant s <= l;
  loop invariant k <= -3;
  loop invariant 0 <= s;
  loop invariant k == -6 || k == -3;
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35 && s <= l && ((s == 0) ==> (k == -6)) && ((s > 0) ==> (k == -3)));
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35 && s >= 0);
  loop invariant s >= 0;
  loop invariant s <= l && (k == -6 || k == -3) && l == 35 && b == \at(b, Pre) && m == \at(m, Pre);
  loop assigns k, s;
*/
while (s<l) {
      k = k-k;
      k = k+(-3);
      s = s+1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 35;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (s % 3) == (l % 3);
  loop invariant 0 <= s;
  loop invariant s <= l;
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35 && s <= l);
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35 && s >= 0);

  loop assigns s;
*/
while (s>=3) {
      s = s-3;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 35;
  loop invariant k == -3;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant s <= l;
  loop invariant 0 <= s;
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35 && s >= 0);
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && l == 35);
  loop invariant s >= 0;

  loop assigns s;
*/
while (s<=k-1) {
      s = s+1;
  }

}
