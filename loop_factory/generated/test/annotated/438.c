int main1(int e,int u){
  int fw, i3, o, cy, n4kv;
  fw=46;
  i3=3;
  o=0;
  cy=0;
  n4kv=fw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cy == o*(o-1)/2;
  loop invariant e == \at(e, Pre) + o*(fw - i3);
  loop invariant 0 <= o <= fw;
  loop assigns cy, e, o;
*/
while (o<fw) {
      cy = cy + o;
      e = e+fw-i3;
      o = o + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= o <= fw;
  loop assigns cy, o, n4kv;
*/
while (o<i3) {
      cy = i3-o;
      o += 4;
      n4kv += i3;
  }
}