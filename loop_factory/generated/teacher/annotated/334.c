int main1(int a,int k){
  int o, t, v;

  o=55;
  t=o;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant t >= 0;
  loop invariant t <= 55;
  loop invariant v == -4 || v == 0 || v == 2;
  loop invariant (t == 55) ==> (v == -4);
  loop invariant o == 55;
  loop invariant v >= -4;
  loop invariant v <= 2;

  loop assigns t, v;
*/
while (t>0) {
      v = v-v;
      v = v+v;
      if (t+1<=a+o) {
          v = v+2;
      }
      t = t-1;
  }

}
