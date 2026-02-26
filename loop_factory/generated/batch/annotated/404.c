int main1(int k,int q){
  int o, l, t, s;

  o=57;
  l=0;
  t=o;
  s=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((t - o) % 4) == 0;
  loop invariant o - 3 <= t;
  loop invariant t <= o + 3;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o == 57;
  loop invariant t % 4 == o % 4;
  loop invariant t <= o;
  loop invariant (t - o) % 4 == 0;
  loop invariant t >= o;
  loop assigns t;
*/
while (t<o) {
      if (t<o) {
          t = t+1;
      }
      t = t+3;
  }

}
