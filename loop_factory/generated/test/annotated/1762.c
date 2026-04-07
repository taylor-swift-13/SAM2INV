int main1(){
  int nr, l9, y, f88;
  nr=1;
  l9=nr;
  y=l9;
  f88=l9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l9 == y;
  loop invariant f88 == 1 + ((y - 1) / 2);
  loop assigns y, f88, l9;
*/
while (l9-3>=0) {
      y++;
      f88 = f88+(y%2);
      l9 = l9 + 1;
  }
}