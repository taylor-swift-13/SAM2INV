int main1(int k){
  int l, i, r, v;

  l=44;
  i=2;
  r=i;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r + v == -6;
  loop invariant i == 2;
  loop invariant l == 44;
  loop invariant r >= 2;
  loop invariant v <= -8;
  loop invariant k == \at(k, Pre);
  loop invariant r - i >= 0;
  loop invariant i <= l - 1;
  loop assigns r, v;
*/
while (i<=l-2) {
      r = r+1;
      v = v-1;
  }

}
