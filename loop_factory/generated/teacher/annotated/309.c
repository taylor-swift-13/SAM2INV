int main1(int a,int m){
  int l, h, v;

  l=m;
  h=4;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(m, Pre);
  loop invariant h == 4;
  loop invariant v == 0 || v == 4;
  loop invariant a == \at(a, Pre);
  loop invariant l == m;
  loop invariant m == \at(m, Pre);

  loop invariant v >= 0;
  loop invariant v <= 4;

  loop assigns v;
*/
while (h+1<=l) {
      v = v+4;
      v = v-v;
  }

}
