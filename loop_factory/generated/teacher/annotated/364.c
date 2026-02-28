int main1(int k,int q){
  int o, l, t, s;

  o=57;
  l=0;
  t=o;
  s=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 57;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= o;
  loop invariant (t - o) % 4 == 0;
  loop invariant s >= k;
  loop invariant t <= o + 3;
  loop invariant t <= o;
  loop invariant t >= 0;
  loop invariant t == o;
  loop invariant s == k;
  loop assigns t, s;
*/
while (t<o) {
      if (t<o) {
          t = t+1;
      }
      t = t+3;
      s = s+t;
      s = s+s;
  }

}
