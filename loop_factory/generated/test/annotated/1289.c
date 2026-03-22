int main1(int s){
  int f9r, t42, jg, ko;
  f9r=(s%21)+13;
  t42=0;
  jg=s;
  ko=t42;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s,Pre) + t42*(t42 - 1)/2;
  loop invariant jg == \at(s,Pre) + 2 * t42;
  loop invariant ko == t42 * (t42 + \at(s,Pre));
  loop invariant f9r == (\at(s, Pre) % 21) + 13;
  loop assigns s, t42, jg, ko;
*/
for (; t42<=f9r-1; t42 += 1) {
      jg += 1;
      ko = ko + jg;
      s += t42;
      jg += 1;
  }
}