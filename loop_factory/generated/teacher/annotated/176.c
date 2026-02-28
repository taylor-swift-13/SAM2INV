int main1(int b,int m){
  int l, s, k;

  l=35;
  s=0;
  k=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == -3 || (s == 0 && k == -6);
  loop invariant 0 <= s;
  loop invariant s <= l;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == 35;
  loop invariant (s > 0) ==> (k == -3);
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre));
  loop assigns k, s;
*/
while (s<l) {
      k = k-k;
      k = k+(-3);
      s = s+1;
  }

}
