int main1(int a,int k){
  int h, t, s, c;

  h=8;
  t=1;
  s=5;
  c=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant h == 8;
  loop invariant 0 <= s <= 5;
  loop invariant t >= 1;
  loop invariant c >= 1;
  loop invariant c == 1 + ((t - 1) * (t - 2)) / 2;
  loop invariant s == 0 || s == 5;
  loop invariant c == 1 + (t - 1) * (t - 2) / 2;
  loop invariant s >= 0;
  loop assigns s, c, t;
*/
while (1) {
      s = s+1;
      c = c-1;
      c = c+t;
      s = s-s;
      t = t+1;
  }

}
