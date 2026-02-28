int main1(int m){
  int p, i, v;

  p=66;
  i=p;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= 66;
  loop invariant i >= 0;
  loop invariant i % 3 == 0;
  loop invariant v == -3 || v == 0 || v == 1;
  loop invariant m == \at(m, Pre);
  loop invariant p == 66;

  loop invariant 0 <= i;
  loop invariant i <= p;
  loop invariant (v == -3) || (v == 0) || (v == 1);
  loop invariant i % 3 == p % 3;
  loop invariant (i == 66 && v == -3) || ((m > -2 && v == 1) || (m <= -2 && v == 0));
  loop assigns v, i;
*/
while (i>2) {
      v = v-v;
      if (v<m+2) {
          v = v+1;
      }
      i = i-3;
  }

}
