int main1(int h){
  int md, su, e9, c;
  md=10;
  su=1;
  e9=md;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant md == 10;
  loop invariant su <= md;
  loop invariant (c == 0) || (su == md && e9 == c*c);
  loop invariant (c == 0 ==> e9 == md) && (c > 0 ==> e9 == c*c);
  loop invariant (0 <= c);
  loop invariant (c <= 1);
  loop assigns c, e9, su;
*/
while (1) {
      if (!(su<md)) {
          break;
      }
      c = c + 1;
      e9 = c*c;
      su = md;
  }
}