int main1(int a,int k){
  int o, t, v;

  o=55;
  t=o;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 55;
  loop invariant 0 <= t;
  loop invariant t <= o;
  loop invariant v == 0 || v == -4;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant t >= 0;
  loop invariant t <= 55;
  loop invariant (t < 55) ==> (v == 0);
  loop invariant v == 0 || (v == -4 && t >= 1);
  loop assigns t, v;
*/
while (t>0) {
      v = v-v;
      t = t-1;
  }

}
