int main1(int v){
  int l, h63d, xwn2, c4zl, jx;
  l=v+4;
  h63d=0;
  xwn2=l;
  c4zl=1;
  jx=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xwn2 == l;
  loop invariant h63d >= 0;
  loop invariant c4zl == 1 + h63d * xwn2;
  loop invariant jx == l + h63d;
  loop invariant (l < 0) || (h63d <= l);
  loop assigns jx, c4zl, h63d;
*/
while (h63d < l) {
      jx++;
      c4zl = c4zl + xwn2;
      h63d = h63d + 1;
  }
}