int main1(int a,int b){
  int x, c, v, o;

  x=40;
  c=x;
  v=c;
  o=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 0;
  loop invariant c <= x;
  loop invariant v == x + 4*(x - c);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant x == 40;
  loop invariant v == 200 - 4*c;
  loop invariant v + 4 * c == 200;
  loop invariant c <= 40;
  loop invariant 0 <= c;
  loop invariant 40 <= v && v <= 200;
  loop assigns v, c;
*/
while (c>0) {
      v = v+4;
      c = c-1;
  }

}
