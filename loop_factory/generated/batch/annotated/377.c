int main1(int k,int n){
  int s, i, v;

  s=37;
  i=1;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 37;
  loop invariant i == 1;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == 0 || v == 1;
  loop invariant 0 <= v <= 1;
  loop invariant i <= s;
  loop invariant 0 <= v;
  loop invariant v <= 1;
  loop invariant (v == 0) || (v == 1) && v <= i && i <= s;
  loop assigns v;
*/
while (i<s) {
      v = v+4;
      v = v-v;
  }

}
