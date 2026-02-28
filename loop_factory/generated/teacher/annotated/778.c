int main1(int b,int q){
  int r, o, v, f;

  r=(q%30)+18;
  o=0;
  v=-3;
  f=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant v == -3 + 7*o;
  loop invariant f == r + 2*o;
  loop invariant r == (\at(q, Pre) % 30) + 18;
  loop invariant o >= 0;
  loop invariant r == (q % 30) + 18;
  loop invariant 0 <= o;
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);

  loop assigns v, o, f;
*/
while (1) {
      if (o>=r) {
          break;
      }
      v = v+1;
      o = o+1;
      v = v+5;
      f = f+2;
      v = v+1;
  }

}
