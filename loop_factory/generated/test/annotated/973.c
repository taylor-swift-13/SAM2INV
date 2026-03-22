int main1(){
  int o, t9, y7, v7e, c;
  o=11;
  t9=0;
  y7=t9;
  v7e=t9;
  c=t9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y7 == t9;
  loop invariant v7e == t9;
  loop invariant c == (t9 * (t9 + 7)) / 2;
  loop invariant t9 <= o;
  loop assigns c, t9, y7, v7e;
*/
while (1) {
      y7 += 1;
      v7e = (1)+(v7e);
      c += v7e;
      c = c + 3;
      t9 += 1;
      if (t9>=o) {
          break;
      }
  }
}