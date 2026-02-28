int main1(int k,int m){
  int l, j, v;

  l=15;
  j=4;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (k == \at(k, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant (l == 15);
  loop invariant (4 <= j && j <= l);
  loop invariant (v >= l);
  loop invariant 4 <= j;
  loop invariant j <= l;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v >= 15;
  loop invariant v <= 114;
  loop invariant (k + l < 8) ==> v == 15;
  loop invariant (j <= k + l - 3) ==> v == 15 + (j + 3) * (j - 4) / 2;
  loop invariant (4 <= j);
  loop invariant (j <= l);
  loop invariant (v <= 114);
  loop invariant v <= 15 + ((j + 3) * (j - 4)) / 2;
  loop assigns j, v;
*/
while (j<l) {
      if (j+4<=k+l) {
          v = v+j;
      }
      j = j+1;
  }

}
