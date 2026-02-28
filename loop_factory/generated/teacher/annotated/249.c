int main1(int p,int q){
  int k, i, v;

  k=34;
  i=k;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant i <= k;
  loop invariant v == 0 || (i == k && v == -8);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant k == 34;
  loop invariant i <= 34;
  loop invariant v <= 0;
  loop invariant 0 <= i;
  loop assigns i, v;
*/
while (i>0) {
      if (v+5<k) {
          v = v+5;
      }
      v = v-v;
      i = i-1;
  }

}
