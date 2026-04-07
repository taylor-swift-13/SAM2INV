int main1(int l){
  int dr, ck, f7, ol;
  dr=l*5;
  ck=1;
  f7=l;
  ol=l*2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dr == 5 * \at(l, Pre);
  loop invariant ol >= 2 * \at(l, Pre);
  loop invariant (ck == 1) || (ck == dr);
  loop assigns l, ol, f7, ck;
*/
while (ck<dr) {
      ol = ol + 1;
      f7 = ol*ol;
      l = l + f7;
      ck = dr;
  }
}