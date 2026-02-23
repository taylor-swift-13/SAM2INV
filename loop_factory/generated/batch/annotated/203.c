int main1(int a,int q){
  int t, v, i, w;

  t=42;
  v=t;
  i=-5;
  w=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 42;
  loop invariant v == 42;
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant i >= -5;
  loop invariant i <= t + 1;
  loop invariant v == t;
  loop invariant (i + 5) % 2 == 0;
  loop invariant v >= 1;
  loop assigns i;
*/
while (v-1>=0) {
      if (i+1<=t) {
          i = i+1;
      }
      else {
          i = t;
      }
      i = i+1;
  }

}
