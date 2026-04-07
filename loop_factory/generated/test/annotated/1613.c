int main1(){
  int x8, g3x, b, o, v, i;
  x8=1;
  g3x=x8;
  b=0;
  o=0;
  v=-6;
  i=g3x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == o;
  loop invariant v == -6 + o;
  loop invariant 0 <= o;
  loop invariant o <= x8;
  loop invariant i == 1 + b*(b+1)/2;
  loop invariant x8 == 1;
  loop assigns b, i, o, v;
*/
while (o<x8) {
      o = o + 1;
      v++;
      b += 1;
      i += b;
  }
}