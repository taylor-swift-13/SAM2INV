int main1(){
  int ly, ea0g, cet, w, kv, l6;
  ly=62;
  ea0g=ly;
  cet=0;
  w=3;
  kv=0;
  l6=ly;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ly == 62;
  loop invariant l6 >= 62;
  loop invariant cet >= 0;
  loop invariant ea0g >= 0;
  loop invariant w >= 3;
  loop invariant cet <= l6 - 1;
  loop invariant cet + ea0g == 62;
  loop assigns w, l6, cet, ea0g;
*/
while (ea0g>0) {
      w += cet;
      l6 = l6 + 1;
      cet = cet + ea0g;
      ea0g = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cet <= l6;
  loop invariant ea0g >= 0;
  loop invariant ly == 62;
  loop invariant l6 >= 63;
  loop invariant w >= 3;
  loop invariant kv >= 0;
  loop assigns kv, ea0g, w, cet;
*/
while (cet<=l6-1) {
      kv = kv + w;
      ea0g = ea0g + kv;
      w = w*4;
      cet = l6;
  }
}